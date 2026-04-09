{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Backend.PVS (translate, prettyPrint) where

import Lib (TranslError, Ident)

import Control.Monad (void)
import Control.Monad.Except (Except, runExcept)
import Control.Monad.Error.Class (MonadError)
import Language.C (NodeInfo)
import Data.Scientific (Scientific)
import Data.Maybe (catMaybes)
import System.Exit (die)

import qualified Intermediate.Func as F
import qualified AbsPVSLang as P
import qualified Operators as P
import qualified PPExt as P
import Text.Printf (printf)

import System.FilePath (takeBaseName)


newtype PVSTransl p a = PVSTransl {unTrans :: Except (TranslError p) a}
  deriving
    ( Functor,
      Applicative,
      Monad,
      MonadError (TranslError p)
    )

type Transl = PVSTransl NodeInfo


translType ::  F.FType -> Transl P.PVSType
translType F.TInt              = return P.TInt
translType F.TFloat            = return P.FPSingle
translType F.TDouble           = return P.FPDouble
translType F.TBool             = return P.Boolean
translType (F.TTuple (t1,t2))  = P.Tuple <$> mapM translType [t1,t2]
translType (F.TFun argTys ty)  = P.TypeFun <$>
                                  mapM translType argTys <*>
                                  translType ty
translType (F.TRecord flds)    = P.Record <$> traverse (traverse translType) flds
translType (F.TVector ty _)    = do
  ty' <- translType ty
  return $ P.Array [P.TInt] ty'
translType (F.TSyn _ ty)       = translType ty
translType ty = error $ show ty
-- [TODO] throw error here


translOp :: F.Op -> Transl P.BinOp
translOp F.Add = return P.AddOp
translOp F.Sub = return P.SubOp
translOp F.Mul = return P.MulOp
translOp F.Div = return P.DivOp
translOp _ = undefined
-- [TODO] throw error here


readRational :: String -> Rational
readRational str = toRational (read str :: Scientific)

translExp :: F.Exp a -> Transl P.FAExpr
translExp (F.Var _ id' ty) = P.FVar <$> translType ty <*> pure id'
translExp (F.EFloat _ fStr) = return $ P.FCnst P.FPSingle (readRational fStr)
translExp (F.EDouble _ fStr) = return $ P.FCnst P.FPDouble (readRational fStr)
translExp (F.EInt _ n) = return $ P.FInt (toInteger n)
translExp (F.ELet _ id' ty val e) = do
  ty' <- translType ty
  val' <- translExp val
  e' <- translExp e
  return $ P.Let [(id',ty',val')] e'
-- [TODO] handle implicit casting
translExp e@(F.Infix _ e1 op e2) =
  case F.binOpType (void e) of
    Just ty ->
      P.BinaryFPOp <$> translOp op <*> translType ty <*> translExp e1  <*> translExp e2
    Nothing ->
      error "can't infer type"
translExp (F.FuncCall _ (F.Var _ funId (F.TFun _ retTy)) args) =
  P.FEFun False funId P.ResValue <$> translType retTy <*> mapM translExp args
translExp (F.EVecRead _ id' ty ix) = 
  P.FArrayElem <$> translType ty <*> pure id' <*> mapM translExp [ix]
translExp (F.EVecWrite {}) = error "vector writes not supported within scalar functions" 
translExp e = error $ show (void e)


translCollExp :: F.Exp a -> Transl P.CollFAExpr
translCollExp (F.Var _ id' ty) =
  P.CollVar <$> translType ty <*> pure id'
translCollExp (F.ELet _ id' ty val e ) = do
  ty' <- translType ty
  val' <- translExp val
  e' <- translCollExp e
  return $ P.CLet [(id', ty', val')] e'
translCollExp (F.EVecWrite _ id' vTy fld val) = do
  vTy' <- translType vTy
  P.ArrayUpdate (P.CollVar vTy' id') <$> translExp fld <*> translExp val
translCollExp (F.FuncCall _ (F.Var _ funId (F.TFun _ retTy)) args) =
      P.CollFun False funId <$> translType retTy <*> mapM translExp args
translCollExp (F.FuncCall {}) = error "lambda calls not supported yet"
translCollExp _ = undefined

translate :: [F.TLD a] -> IO P.Program
translate tlds = either (die . show) return (runTrns prog)
  where
    prog = catMaybes <$> mapM translTld (filterMain tlds)
    runTrns :: PVSTransl p a -> Either (TranslError p) a
    runTrns = runExcept  . unTrans

filterMain :: [F.TLD a] -> [F.TLD a] 
filterMain = filter (not . isMain)
  where
    isMain (F.TLFuncDecl funDecl) = F.funId funDecl == "main"
    isMain _ = False

prettyPrint :: FilePath -> P.Program -> String
prettyPrint file prog = header ++ progString ++ footer
  where
    progString = show $ P.prettyDoc prog
    moduleName = takeBaseName file
    header = printf "%s: THEORY\nBEGIN\nIMPORTING float@aerr754dp\n\n" moduleName
    footer = printf "\n\nEND %s" moduleName

translTld :: F.TLD a -> Transl (Maybe P.Decl)
translTld (F.TLFuncDecl fDecl) = sequence $ Just $ do
  fTy <- translType (F.funTy fDecl)
  case fTy of
    P.TypeFun _ retTy -> do -- Function declaration
      args <- mapM translArg (F.funArgsTys fDecl)
      if isCollType retTy
        then P.CollDecl False retTy (F.funId fDecl) args <$>
               translCollExp (F.funBody fDecl)
        else P.Decl False retTy (F.funId fDecl) args <$>
               translExp (F.funBody fDecl)
    _ -> -- Variable Declaration
      if isCollType fTy
        then P.CollDecl False <$> 
              translType (F.funRetTy fDecl) <*>
              pure (F.funId fDecl) <*>
              pure [] <*>
              translCollExp (F.funBody fDecl)
        else P.Decl False <$>
              translType (F.funRetTy fDecl) <*>
              pure (F.funId fDecl) <*>
              pure [] <*>
              translExp (F.funBody fDecl)
  where            
    translArg :: (Ident, F.FType) -> Transl P.Arg
    translArg (id',fTy) = P.Arg id' <$> translType fTy
translTld (F.TLTypeSyn {}) = return Nothing

isCollType :: P.PVSType -> Bool
isCollType (P.Array {})  = True
isCollType (P.List {})   = True
isCollType (P.Tuple {})  = True
isCollType (P.Record {}) = True
isCollType _             = False


{-# LANGUAGE GADTs #-}
module Backend.PVS.PVSTranslator (translatePVS, PVSOutput (..), P.Program) where

import Lib (Ident)
import Error (throwTranslErrMsg)
import Backend.Backend (BackendM, backendOption)
import Intermediate.FuncPretty (pp)
import qualified Intermediate.Func as F
import qualified AbsPVSLang as P
import qualified Operators as P

import Control.Monad (void)
import Language.C (NodeInfo)
import Data.Scientific (Scientific)
import Data.Maybe (catMaybes)
import Text.Printf (printf)
import Data.List (intercalate)



type Transl a = BackendM NodeInfo a

data PVSOutput = PVSOutput {
                  pvsProgram :: P.Program,
                  pvsDotInput :: String
                }


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

translUnOp :: F.Op -> Transl P.UnOp
translUnOp F.Sub = return P.NegOp
translUnOp _     = undefined


readRational :: String -> Rational
readRational str = toRational (read str :: Scientific)

expType :: P.FAExpr -> Transl P.PVSType
expType (P.FInt _)                 = return P.TInt
expType (P.FCnst ty _)             = return ty
expType (P.FInterval ty _ _)       = return ty
expType (P.FEFun _ _ _ ty _)       = return ty
expType (P.FVar ty _)              = return ty
expType (P.StructVar ty _)         = return ty
expType (P.FArrayElem ty _ _)      = return ty
expType (P.FListElem ty _ _)       = return ty
expType (P.FTupleElem ty _ _)      = return ty
expType (P.FRecordElem ty _ _)     = return ty
expType (P.TypeCast _ toTy _)      = return toTy
expType (P.ToFloat ty _)           = return ty
expType (P.Value e)                = expType e
expType (P.BinaryFPOp _ ty _ _)    = return ty
expType (P.UnaryFPOp _ ty _)       = return ty
expType (P.FFma ty _ _ _)          = return ty
expType (P.FMap ty _ _)            = return ty
expType (P.FFold ty _ _ _ _)       = return ty
expType (P.Let _ body)             = expType body
expType (P.Ite _ t _)              = expType t
expType _                          = undefined



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
translExp (F.EUnOp _ op e) = do
  e' <- translExp e
  P.UnaryFPOp <$> translUnOp op <*> expType e' <*> pure e'
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

translatePVS :: [F.TLD a] -> Transl PVSOutput
translatePVS tlds = do
  ep <- backendOption "entryPoint"
  case ep of
    Nothing    -> throwTranslErrMsg "(PVS) No entry point provided"
    Just entry ->
      let prog = catMaybes <$> mapM translTld (filter keep tlds)
          keep (F.TLFuncDecl funDecl) = F.funId funDecl == entry
          keep _                      = True
      in PVSOutput <$> prog <*> genDotInput entry tlds

genDotInput :: Ident -> [F.TLD a] -> Transl String
genDotInput entryId tlds =
  case entryFun of
    []          -> throwTranslErrMsg $ printf "Entry point (%s) does not exist" entryId
    [entryFun'] -> spec entryFun'
    _           -> undefined -- should never get here
  where
    spec :: F.FuncDecl a -> Transl String
    spec fDec =
      printf "%s(%s):%s"
        entryId
        (intercalate "," $ fst <$> F.funArgsTys fDec) <$>
        translPreConds (F.funPreconds fDec)
    entryFun =
      [ funDecl
      | (F.TLFuncDecl funDecl) <- tlds,
         F.funId funDecl == entryId ]

translPreConds :: [F.Exp a] -> Transl String
translPreConds = fmap (intercalate ",") . mapM translPreCond
  where
    translPreCond :: F.Exp a -> Transl String
    translPreCond (F.ECompRel _ min' _ e _ max') =
      return $ printf "%s in [%s, %s]" (pp e) (pp min') (pp max')
    translPreCond _ = undefined

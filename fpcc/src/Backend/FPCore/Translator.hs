{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Backend.FPCore.Translator where

import Lib (TranslError, throwTranslErr)

import Intermediate.Func
import Language.C (NodeInfo)
import qualified Backend.FPCore.AST as FP

import Control.Monad.Except (Except, runExcept)
import Control.Monad.Error.Class (MonadError)
import System.Exit (die)
import Data.Functor ((<&>))

newtype FPCoreTransl p a = FPCoreTransl {unTrans :: Except (TranslError p) a}
  deriving
    ( Functor,
      Applicative,
      Monad,
      MonadError (TranslError p)
    )


type Transl = FPCoreTransl NodeInfo


translOp :: Op -> FP.Operation
translOp Add = FP.Plus
translOp Sub = FP.Minus
translOp Mul = FP.Mult
translOp Div = FP.Div
translOp Eq = FP.Eq
translOp Or = FP.Or
translOp And = FP.And
translOp Neq = FP.NEq
translOp LtEq = FP.LtEq
translOp Gt = FP.Gt
translOp Lt = FP.Lt


translExp :: Exp NodeInfo -> Transl FP.Expr
translExp (Var _ id' _) = return $ FP.EVar id'
translExp (Infix _ e1 op e2) =
  FP.EOp (translOp op) <$> mapM translExp [e1, e2]
translExp (ECompRel _ b1 op1 e op2 b2) = 
  if op1 == op2
    then FP.EOp (translOp op1) <$> mapM translExp [b1, e, b2]
    else do
      b1' <- translExp b1
      e' <- translExp e
      b2' <- translExp b2
      return $ FP.EOp 
                FP.And [FP.EOp (translOp op1) [b1', e'],
                        FP.EOp (translOp op2) [e', b2']] 
translExp (EInt _ n) = return $ FP.ENumber (FP.NumInteger $ toInteger n)
translExp (EFloat _ f) = return $ FP.ENumber (FP.NumDecimal f)
translExp (EDouble _ f) = return $ FP.ENumber (FP.NumDecimal f)
translExp (EBool _ True) = return $ FP.EConst FP.ConstTRUE
translExp (EBool _ False) = return $ FP.EConst FP.ConstFALSE
translExp (EIte _ cond then' else') =
  FP.EIf <$> translExp cond <*> translExp then' <*> translExp else'
translExp  (ELet _ id' _ val body) = do
  val' <- translExp val
  body' <- translExp body
  return $ FP.ELet [(id', val')] body'
translExp (FuncCall _ (Var _ fId _) args) = do
  FP.EOp (FP.CustOp fId) <$> mapM translExp args
translExp (FuncCall n _ _) = throwTranslErr "Function call with something other than identifier" n
translExp e = error $ show e


translProg :: [TLD NodeInfo] -> Transl FP.FPCoreProg
translProg = mapM translTLD
  where
    translTLD :: TLD NodeInfo -> Transl FP.FPCore
    translTLD (TLFuncDecl funcDecl) = do
      let funName = Just (funId funcDecl)
      let params = fst <$> funArgsTys funcDecl
      props' <- mapM translPrec (funPreconds funcDecl)
      body <- translExp (funBody funcDecl)
      return $ FP.FPCore {
        FP.fpcoreName = funName,
        FP.fpcoreParams = params,
        FP.fpcoreProperties = props',
        FP.fpcoreBody = body
      }
    translTLD (TLTypeSyn n _ _) = throwTranslErr "Type synonyms not supported" n
    translPrec :: Exp NodeInfo -> Transl FP.Property
    translPrec prec = translExp prec <&> FP.Property ":pre"


translate :: [TLD NodeInfo] -> IO FP.FPCoreProg
translate prog =
   either (die . show) return (trns $ translProg prog)
  where
    trns :: Transl a -> Either (TranslError NodeInfo) a
    trns = runExcept . unTrans

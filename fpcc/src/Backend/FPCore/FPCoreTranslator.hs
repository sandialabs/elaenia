module Backend.FPCore.FPCoreTranslator where

import Lib (Ident)
import Error (throwTranslErr, throwTranslErrMsg)

import Intermediate.Func
import Language.C (NodeInfo)
import qualified Backend.FPCore.AST as FP
import Backend.Backend (BackendM)

import Data.Functor ((<&>))
import Data.Maybe (catMaybes)
import Control.Monad (void)


type Transl a = BackendM NodeInfo a


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
translExp (EUnOp _ op e) = FP.EOp (translOp op) . (:[]) <$> translExp e
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
translExp (EVec _ exps) = FP.EArray <$> mapM translExp exps
translExp (EVecRead _ id' _ ix) = do
  ix' <- translExp ix
  return $ ref [FP.EVar id', ix']
translExp e@(EVecWrites _ id' vTy ix es) = do
  size <- vectorSize vTy
  (FP.ENumber (FP.NumInteger nIx)) <- translExp ix
  es' <- mapM translExp es
  return $ FP.EArray $ 
    (arrElem id' <$> [0..nIx - 1]) ++ 
    es' ++ 
    (arrElem id' <$> [nIx + fromIntegral (length es') .. size - 1])
translExp (EVecWrite _ id' vTy ix e) = do
  size <- vectorSize vTy
  (FP.ENumber (FP.NumInteger nIx)) <- translExp ix
  e' <- translExp e
  return $ insertIntoArray id' nIx [e'] size
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

vectorSize :: FType -> Transl Integer
vectorSize (TVector _ size)          = return size
vectorSize (TSyn _ (TVector _ size)) = return size
vectorSize _                         = throwTranslErrMsg "Cannot infer size of vector"

insertIntoArray :: Ident -> Integer -> [FP.Expr] -> Integer -> FP.Expr
insertIntoArray arrId ix elms size = FP.EArray elems
  where
    elems :: [FP.Expr]
    elems =
      (arrElem arrId <$> [0 .. ix - 1]) ++
      elms ++
      (arrElem arrId <$> [ix + lenElms .. (size - 1)])
      where
        lenElms = toInteger (length elms)

arrElem :: Ident -> Integer -> FP.Expr
arrElem arrId ix' = ref [FP.EVar arrId, FP.ENumber (FP.NumInteger ix')]

ref :: [FP.Expr] -> FP.Expr
ref = FP.EOp (FP.CustOp "ref")


translateFPCore :: [TLD NodeInfo] -> Transl FP.FPCoreProg
translateFPCore = (catMaybes <$>) . mapM translTLD
  where
    translTLD :: TLD NodeInfo -> Transl (Maybe FP.FPCore)
    translTLD (TLFuncDecl funcDecl) = do
      let funName = Just (funId funcDecl)
      let params = fst <$> funArgsTys funcDecl
      props' <- mapM translPrec (funPreconds funcDecl)
      body <- translExp (funBody funcDecl)
      return $ Just $  FP.FPCore {
        FP.fpcoreName = funName,
        FP.fpcoreParams = params,
        FP.fpcoreProperties = props',
        FP.fpcoreBody = body
      }
    translTLD (TLTypeSyn n _ _) = return Nothing
    translPrec :: Exp NodeInfo -> Transl FP.Property
    translPrec prec = translExp prec <&> FP.Property ":pre"





module Imp.TypeChecker (typeCheckImp) where

import qualified Data.Map as M
import Control.Monad
import Text.Printf
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.State
import Text.Parsec.Pos (SourcePos)


import Lib
import Imp.Parser hiding (Exp, Statement) 
import Imp.AST hiding (Exp, Statement)
import qualified Imp.AST as AST

type Exp = AST.Exp SourcePos
type Statement = AST.Statement SourcePos

type Gamma = M.Map Ident IType

type TypeError = (String, SourcePos)

type TypeChecker = ExceptT TypeError (State Gamma)

addType :: Ident -> IType -> TypeChecker ()
addType id ty = modify $ M.insert id ty

getType :: Ident -> SourcePos -> TypeChecker IType
getType id' pos = do
  env <- get
  case M.lookup id' env of
    Just ty -> return ty
    _       -> throwError (id' ++ " Identifier not found", pos)

localScope :: TypeChecker a -> TypeChecker a
localScope action = do
  originalSt <- get
  ret <- action
  put originalSt
  return ret

errMsg :: IType -> IType -> String  
errMsg t1 t2 = printf "Could not match expected type (%s) and actual type (%s)" (show t1) (show t2)


typeCheckStatement :: Statement -> TypeChecker IType
typeCheckStatement (VarDecl pos ty id' e) = do
  eTy <- typeCheckExp e
  unless (ty == eTy) (throwError $ (errMsg ty eTy, pos))
  _ <- addType id' ty
  return TVoid
typeCheckStatement (If pos pred then' else') = do
  predTy <- typeCheckExp pred
  case predTy of
    TBool -> do
      mapM_ typeCheckStatement then'
      mapM_ typeCheckStatement else'
      return TVoid
    _     -> throwError ("'if' predicate not a boolean", pos)
typeCheckStatement (Ass pos id' exp) = do
  ty <- getType id' pos
  eTy <- typeCheckExp exp
  unless (ty == eTy) (throwError $ (errMsg ty eTy, pos))
  return TVoid
typeCheckStatement (Return _ _) = return TVoid
typeCheckStatement (SExp _ e) = typeCheckExp e
typeCheckStatement fun@(Func (FuncDecl _ id' argsTys retTy body)) = do
  localScope (do 
    mapM_ (\(id',ty) -> addType id' ty) argsTys
    mapM_ typeCheckStatement body
    mapM_ (typeCheckReturn retTy) [ret | ret@(Return _ _) <- body])
  addType id' (TFun (snd <$> argsTys) retTy)
  return $ TFun (snd <$> argsTys) retTy


typeCheckReturn :: IType -> Statement -> TypeChecker ()
typeCheckReturn retTy (Return p exp) = do
  ty <- typeCheckExp exp
  if (ty == retTy) 
    then return ()
    else throwError ("Return type does not match function", p)
typeCheckReturn _ _ = undefined -- should never reach here

typeCheckExp :: Exp -> TypeChecker IType
typeCheckExp (Var pos id') = getType id' pos
typeCheckExp (EString _ _) = return TString
typeCheckExp (EChar _ _) = return TChar
typeCheckExp (EBool _ _) = return TBool
typeCheckExp (EInt _ _) = return TInt
typeCheckExp (Infix p e1 Eq e2) = do
  t1 <- typeCheckExp e1
  t2 <- typeCheckExp e2
  if (t1 == t2) 
    then return TBool
    else throwError ("Types in equality don't match.",p)
typeCheckExp (Infix _ _ _ _) = return TInt
typeCheckExp (FunCall _ "print" _) = return TVoid
typeCheckExp (FunCall p id' args) = do
  funTy <- getType id' p
  case funTy of
    TFun paramTys retTy -> do
      argTys <- mapM typeCheckExp args
      if argTys == paramTys 
        then return retTy
        else throwError ("Function arguments incorrectly typed.",p)
    _ -> throwError ("(" ++ id' ++ ")" ++ " not a function.", p)

typeCheckImp :: [Statement] -> Either String Gamma
typeCheckImp ast = do
  case (runState $ runExceptT $ mapM typeCheckStatement $ ast) (M.empty) of
    (Left err, _) -> Left $ show err
    (Right _, g) -> Right g


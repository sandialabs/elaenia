module Func.TypeChecker where

import Control.Monad
import Control.Monad.Except
import qualified Data.Map as M
import Text.Parsec.Pos (SourcePos,newPos)


import Lib
import Func.AST hiding (Exp,TLD,Lam)
import qualified Func.AST as AST
import Text.Parsec

type Gamma = M.Map Ident FType

type Exp = AST.Exp SourcePos
type TLD = AST.TLD SourcePos
type Lam = AST.Lam SourcePos

type TypeError = String

type TypeChecker = Except TypeError

instance Eq FType where
  TMaybe t1 == TMaybe t2
    | t1 == t2                     = True
    | t1 /= TStar && t2 == TStar   = True
    | otherwise                    = False
  TTuple t1 == TTuple t2
    | t1 == t2                     = True
    | otherwise                    = False
  TInt == TInt                     = True
  TString == TString               = True
  TChar == TChar                   = True
  TBool == TBool                   = True
  TStar == TStar                   = True
  TFun args ret == TFun args' ret' = args == args' && ret == ret'
  _ == _                           = False
  

addId :: Ident -> FType -> Gamma -> Gamma
addId = M.insert

get :: Ident -> Gamma -> FType
get ident env = case M.lookup ident env of
  Just t -> t
  Nothing -> error $ ident ++": not found."

addArgs :: [(Ident,FType)] -> Gamma -> Gamma
addArgs argsTys env =
  foldl (\env (id',ty) -> addId id' ty env) env argsTys



getTLDType :: Gamma -> TLD -> Gamma
getTLDType env tld = case tld of
  FuncDecl _ ident [] retTy _ -> addId ident retTy env
  FuncDecl _ ident argsTys retTy _ -> addId ident (TFun (map snd argsTys) retTy) env

typeCheckProgram :: [TLD] -> TypeChecker ()
typeCheckProgram tlds = mapM_ (typeCheckTLD env) tlds
  where
    env = foldl getTLDType M.empty tlds


errorMessage :: FType -> FType -> SourcePos -> String
errorMessage et at p = "couldn't match expected type (" ++ show et ++")\
                               \ with actual type (" ++ show at ++")\
                               \ at " ++ show p


typeCheckTLD :: Gamma -> TLD -> TypeChecker ()
typeCheckTLD env (FuncDecl p _ argsTys retTy body) = do
  let env' = addArgs argsTys env
  bodyTy <- typeCheckExp env' body
  unless (retTy == bodyTy) (throwError $ errorMessage retTy bodyTy p)
  return ()



typeCheckExp :: Gamma -> Exp -> TypeChecker FType
typeCheckExp env (Var _ ident) = return $ get ident env
typeCheckExp env (Infix p e1 Eq e2) = do
  t1 <- typeCheckExp env e1
  t2 <- typeCheckExp env e2
  if (t1 == t2) 
    then return TBool 
    else throwError $ errorMessage t1 t2 p
typeCheckExp env (Infix p e1 op e2)
  | op == And || op == Or = do
    t1 <- typeCheckExp env e1
    t2 <- typeCheckExp env e2
    unless (t1 == TBool) (throwError $ errorMessage TBool t1 p)
    unless (t2 == TBool) (throwError $ errorMessage TBool t2 p)
    return TBool
  | otherwise = do
    t1 <- typeCheckExp env e1
    t2 <- typeCheckExp env e2
    if t1 == t2
      then return TInt 
      else throwError $ errorMessage t1 t2 p
typeCheckExp env (EJust _ e) = do 
  t <- typeCheckExp env e
  return $ TMaybe t
typeCheckExp _ (ENothing _) = return $ TMaybe TStar
typeCheckExp _ (EInt _ _) = return TInt
typeCheckExp _ (EBool _ _) = return TBool
typeCheckExp _ (EString _ _) = return TString
typeCheckExp env (ENot pos e) = do
  ty <- typeCheckExp env e
  unless (ty == TBool) (throwError $ errorMessage TBool ty pos)
  return TBool
typeCheckExp env (EIte pos p t e) = do
  pTy <- typeCheckExp env p
  tTy <- typeCheckExp env t
  eTy <- typeCheckExp env e
  unless (pTy == TBool) (throwError $ errorMessage TBool pTy pos)
  if (tTy == eTy) 
    then return eTy
    else throwError $ errorMessage tTy eTy pos
typeCheckExp env (ETuple a (l,r)) = do
  t1 <- typeCheckExp env l    
  t2 <- typeCheckExp env r
  return $ TTuple (t1,t2)
typeCheckExp env (ELet _ id' e1 e2) = do
  t1 <- typeCheckExp env e1
  typeCheckExp (addId id' t1 env) e2
typeCheckExp env (ELam p (AST.Lam _ params retTy body)) = do
  bodyTy <- typeCheckExp env' body
  if (retTy == bodyTy) 
    then return (TFun (map snd params) retTy)
    else throwError (errorMessage retTy bodyTy p)
  where
    env' = addArgs params env
typeCheckExp env (FuncCall p (Var _ "fromMaybe") args) = do
  when (length args /= 1) (throwError "fromMaybe takes a single maybe term")
  case args of
    [arg] -> do
      argTy <- typeCheckExp env arg
      case argTy of
        TMaybe ty -> return ty
        ty         -> throwError $ errorMessage (TMaybe TStar) ty p

typeCheckExp env (FuncCall p (Var _ "fst") args) = do
  when (length args /= 1) (throwError "fst takes a single tuple")
  case args of
    [arg] -> do
      ty <- typeCheckExp env arg
      case ty of
        TTuple (t1,t2) -> return t1
        _              -> throwError "argument to fst must be a tuple"
    _     -> undefined
typeCheckExp env (FuncCall p (Var _ "snd") args) = do
  when (length args /= 1) (throwError "snd takes a single tuple")
  case args of
    [arg] -> do
      ty <- typeCheckExp env arg
      case ty of
        TTuple (t1,t2) -> return t2
        _              -> throwError "argument to fst must be a tuple"
    _     -> undefined
typeCheckExp env (FuncCall p exp args) = do
  funTy <- typeCheckExp env exp
  case funTy of
    (TFun paramsTys retTy) -> do
      let argsPos = map getExpPos args
      argTys <- mapM (typeCheckExp env) args 
      _ <- typeCheckArgs paramsTys (zip argTys argsPos)
      return retTy
    _ -> throwError ("Function expected at " ++ show p)

getExpPos :: Exp -> SourcePos  
getExpPos (AST.Var p _) = p
getExpPos (AST.Infix p _ _ _) = p
getExpPos (AST.EInt p _) = p
getExpPos (AST.EBool p _) = p
getExpPos (AST.EIte p _ _ _) = p
getExpPos (AST.ELet p _ _ _) = p
getExpPos (AST.ELam p _) = p
getExpPos (AST.ETuple p _) = p
getExpPos (AST.FuncCall p _ _) = p
getExpPos (AST.EString p _) = p
getExpPos (AST.EJust p _) = p
getExpPos (AST.ENothing p) = p

typeCheckArgs :: [(FType)] -> [(FType,SourcePos)] -> TypeChecker ()
typeCheckArgs paramTys argTys = zipWithM_ typeCheckArg paramTys argTys
  where
    typeCheckArg :: FType -> (FType,SourcePos) -> TypeChecker ()
    typeCheckArg paramTy (argTy,p) = 
      if paramTy == argTy
        then return ()
        else throwError (errorMessage paramTy argTy p)

-- typeCheckOp _ Add = TFun [TInt, TInt] TInt
-- typeCheckOp _ Sub = TFun [TInt, TInt] TInt
-- typeCheckOp _ Mul = TFun [TInt, TInt] TInt
-- typeCheckOp _ Div = TFun [TInt, TInt] TInt
-- typeCheckOp _ Or = TFun [TBool, TBool] TBool
-- typeCheckOp _ And = TFun [TBool, TBool] TBool
-- typeCheckOp _ Eq = undefined -- should be handled at the expression level


typeCheckFunc :: [TLD] -> Either String ()
typeCheckFunc tlds = do
  case (runExcept $ typeCheckProgram tlds) of
    (Left err) -> Left $ show err
    (Right _) -> Right ()    
    
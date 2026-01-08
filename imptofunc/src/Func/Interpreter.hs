module Func.Interpreter (
  interpretFunc
)

where

import qualified Data.Map as M
import Control.Monad.Except
import Control.Monad (foldM)
import Text.Printf

import Text.Parsec.Pos (SourcePos, newPos)

import Lib
import Func.AST



type InterpError = String

type Interp = Except InterpError

type Env = M.Map Ident Val


data Val =
    VInt Int
  | VString String
  | VChar Char
  | VBool Bool
  | VJust Val
  | VTuple (Val,Val)
  | VNothing
  | VFunc ((Lam SourcePos), Env)
  deriving (Show)

instance Eq Val where
  VString s1 == VString s2 = s1 == s2
  VChar c1 == VChar c2     = c1 == c2
  VBool b1 == VBool b2     = b1 == b2
  VInt i1 == VInt i2       = i1 == i2
  VTuple t1 == VTuple t2   = t1 == t2
  _ == _ = False

(|->) :: Env -> (Ident, Val) -> Env
(|->) = flip . uncurry $ M.insert

(+->) :: Env -> [(Ident, Val)] -> Env
(+->) = foldl (|->)

getVal :: Env -> SourcePos -> Ident -> Interp Val
getVal env pos id' = 
  case M.lookup id' env of
    Just val -> return val
    Nothing -> throwError $ printf "Variable %s not found. %s" id' (show pos)


interpTLDs :: [TLD SourcePos] -> Interp Env
interpTLDs tlds = foldM interpTLD M.empty tlds
  where
    interpTLD env tld
      | null (funArgsTys tld)       = do 
        v <- interpExp env (funBody tld)
        return $ env |-> (funId tld, v)
      | otherwise              = return $ env |-> (funId tld, (VFunc (tldLam tld, env)))
    tldLam = Lam <$> funPosition <*> funArgsTys <*> funRetTy <*> funBody
      



interpExp :: Env -> Exp SourcePos -> Interp Val
interpExp env (Var p id') = getVal env p id'
interpExp env (EJust _ e) = do
  e' <- interpExp env e
  return $ VJust e'
interpExp _ (ENothing _) = return VNothing
interpExp env (ENot _ e) = do
  v <- interpExp env e
  case v of
    VBool b -> return $ VBool (not b)
    _       -> undefined -- unreachable
interpExp env (Infix _ e1 op e2) = do
  e1' <- interpExp env e1
  e2' <- interpExp env e2
  case (e1',op,e2') of
    (VInt v1, Add, VInt v2)   -> return (VInt $ v1 + v2)
    (VInt v1, Sub, VInt v2)   -> return (VInt $ v1 - v2)
    (VInt v1, Mul, VInt v2)   -> return (VInt $ v1 * v2)
    (VInt v1, Div, VInt v2)   -> return (VInt $ v1 `div` v2)
    (VBool v1, Or, VBool v2)  -> return (VBool $ v1 || v2)
    (VBool v1, And, VBool v2) -> return (VBool $ v1 && v2)
    (v1, Eq, v2)              -> return $ VBool (v1 == v2)
    _                         -> undefined -- unreachable after typecheckng
interpExp _ (EInt _ i)  = return $ VInt i
interpExp _ (EBool _ b) = return $ VBool b
interpExp _ (EString _ s) = return $ VString s
interpExp env (ETuple _ (l,r)) = do
  vl <- interpExp env l
  vr <- interpExp env r
  return $ VTuple (vl, vr)
interpExp env (ELam _ l) = return $ VFunc (l,env)
interpExp env (EIte _ i t e) = do
  i' <- interpExp env i
  case i' of
    (VBool True)  -> interpExp env t
    (VBool False) -> interpExp env e
    _             -> undefined -- unreachable after typecheckng
interpExp env (ELet _ id' ve e) = do
  v <- interpExp env ve
  interpExp (env |-> (id',v)) e
interpExp env (FuncCall _ (Var _ "fromMaybe") [arg]) = do
  m <- interpExp env arg
  case m of
    (VJust x) -> return x
    _           -> undefined
interpExp env (FuncCall _ (Var _ "fst") [arg]) = do
  e <- interpExp env arg
  case e of
    (VTuple t) -> return $ fst t
    _          -> undefined
interpExp env (FuncCall _ (Var _ "snd") [arg]) = do
  e <- interpExp env arg
  case e of
    (VTuple t) -> return $ snd t
    _          -> undefined
interpExp env (FuncCall _ f args) = do
  f' <- interpExp env f
  case f' of
    (VFunc ((Lam _ argsTys _ body),env')) -> do
      args' <- mapM (interpExp env) args
      interpExp ((M.union env' env) +-> zip (map fst argsTys) args') body
    e -> error $ show e


interpProgram :: [TLD SourcePos] -> Interp Val
interpProgram tlds = do
  env <- interpTLDs tlds
  getVal env (newPos "" 0 0) "main"

interpretFunc ::  [TLD SourcePos] -> IO String
interpretFunc tlds = 
  case (runExcept $ interpProgram tlds) of
    Left err -> return $ show err
    Right res -> return $ show res

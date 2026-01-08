module Imp.Interpreter where

import qualified Data.Map as M
import Control.Monad
import Control.Monad.State
import Control.Monad.Except
import Prelude hiding (pred)
import Text.Parsec.Pos (SourcePos)

import Lib
import Imp.AST


type InterpError = String


type Env = M.Map Ident Val

getVal :: Ident -> Interp Val
getVal id' = do
  env <- get
  case M.lookup id' env of
    Just val -> return val
    Nothing -> throwError (id' ++ ": Variable not found.")

setVal :: Ident -> Val -> Interp ()
setVal id' val = modify $ M.insert id' val

type Interp = ExceptT InterpError (StateT Env IO)

data Val =
    VInt Int
  | VString String
  | VChar Char
  | VBool Bool
  | VFunc (FuncDecl SourcePos)
  | Null
  deriving (Show)

class PrettyPrint a where
  pp :: a -> String

instance PrettyPrint Val where
  pp (VInt i) = show i
  pp (VString s) = "\"" ++ s ++ "\""
  pp (VChar c) = "'" ++ show c ++ "'"
  pp (VBool b) = show b
  pp (VFunc fun) = "function: " ++ (funId fun)
  pp Null = "Null"

instance Eq Val where
  (VInt i) == (VInt i') = i == i'
  (VString s) == (VString s') = s == s'
  (VChar c) == (VChar c') = c == c'
  (VBool b) == (VBool b') = b == b'
  (VFunc _) == (VFunc _) = False
  Null == Null = True

localScope :: Interp a -> Interp a
localScope action = do
  originalSt <- get
  ret <- action
  put originalSt
  return ret

interpProgram :: [Statement SourcePos] -> Interp Val
interpProgram tlds = do
  mapM_ interpTLD tlds
  env <- get
  main <- getVal "main"
  case main of
    (VFunc fun) -> interpBody (funBody fun)
    _ -> throwError ("(main) is not a function")


interpTLD :: Statement SourcePos -> Interp ()
interpTLD (Func fun) = setVal (funId fun) (VFunc fun)
interpTLD (VarDecl _ _ id e) = do
  v <- interpExpr e
  setVal id v
interpTLD (Ass _ id' e) = do
  val <- interpExpr e
  setVal id' val
interpTLD _ = undefined -- Only assignments and function defitions allowed at top leve

interpExpr :: Exp a -> Interp Val
interpExpr (EString _ s) = return $ VString s
interpExpr (EChar _ c) = return $ VChar c
interpExpr (Var _ id') = getVal id'
interpExpr (EInt _ i) = return $ VInt i
interpExpr (EBool _ b) = return $ VBool b
interpExpr (Infix _ e1 Eq e2) = do
  v1 <- interpExpr e1
  v2 <- interpExpr e2
  return $ VBool (v1 == v2)
interpExpr (Infix _ e1 op e2) = do
  v1 <- interpExpr e1
  v2 <- interpExpr e2
  let op' = (case op of
              Add -> (+)
              Sub -> (-)
              Mul -> (*)
              Div -> div)
    in
      case (v1,v2) of
        (VInt v1', VInt v2') -> return $ VInt $ v1' `op'` v2'
        _ -> undefined -- TypeChecker makes this unreachable
interpExpr (FunCall _ "print" args) = do
  argVals <- mapM interpExpr args
  mapM_ (liftIO . putStrLn . pp) argVals
  return Null
interpExpr (FunCall _ fid args) = do
  fun <- getVal fid
  args' <- mapM interpExpr args
  case fun of
    (VFunc fun') ->
      localScope (do
        zipWithM_ setVal (fst <$> (funArgsTys fun')) args'
        interpBody (funBody fun'))
    _ -> undefined  -- TypeChecker makes this unreachable
    

-- modify to allow for variable decl and use local scope as well
interpBody :: [Statement SourcePos] -> Interp Val
interpBody [] = return Null
interpBody ((SExp _ e):res) = interpExpr e >> interpBody res
interpBody ((Return _ e):_) = interpExpr e
interpBody ((Ass _ id' e):rest) = do
  val <- interpExpr e
  setVal id' val
  interpBody rest
interpBody ((If _ pred then' else'):rest) = do
  pred' <- interpExpr pred
  case pred' of
    (VBool True) -> handleCase then' rest
    (VBool False) -> handleCase else' rest
    _ -> undefined -- TypeChecker makes this unreachable
  where
    handleCase now later = do
      res <- interpBody now
      case res of
        Null -> interpBody later
        _    -> return res
interpBody ((Func _):_) = undefined -- Nested function definitions not supported


interpretImp :: [Statement SourcePos] -> IO String
interpretImp ast = do
  interpResult <- (runStateT $ runExceptT $ interpProgram ast) M.empty
  case interpResult of
    (Left err, env) -> return $ show err
    (Right val, env) -> return $ "result: " ++ pp val
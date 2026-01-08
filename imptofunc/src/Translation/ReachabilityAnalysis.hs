module Translation.ReachabilityAnalysis (reachablePaths) where


import Data.SBV
import Imp.AST
import Imp.TypeChecker
import Text.Parsec.Pos (SourcePos)
import qualified Data.Map as M
import Lib
import Text.Printf

data SBVExp = 
  SBVInt (SBV Int32) |
  SBVBool SBool      |
  SBVString SString


type Env = M.Map Ident IType

typeOf :: Env -> Ident -> IType
typeOf env k = case M.lookup k env of
  Nothing -> error $ printf "(%s) not found in typing environment"
  Just ty -> ty

reachablePaths :: [Statement SourcePos] -> [Exp ()] -> IO ThmResult
reachablePaths prog preds = undefined
  where
    env = case typeCheckImp prog of
      Right env' -> env'
      _          -> error "type checking failed"
    -- go :: [Exp ()] -> [Exp ()] -> IO ThmResult

translExp :: Env -> Exp a -> SBVExp
translExp env e = undefined
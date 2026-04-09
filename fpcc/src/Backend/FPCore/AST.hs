module Backend.FPCore.AST where
import GHC.TypeLits (Div)

type Identifier = String

data Number = 
    NumInteger Integer
  | NumDecimal String
  deriving (Eq,Show)

data Constant = 
    ConstE
  | ConstLOG2E
  | ConstLOG10E
  | ConstLN2
  | ConstLN10
  | ConstPI
  | ConstPI_2
  | ConstPI_4
  | ConstM_1_PI
  | ConstM_2_PI
  | ConstM_2_SQRTPI
  | ConstSQRT2
  | ConstSQRT1_2
  | ConstINFINITY
  | ConstNAN
  | ConstTRUE
  | ConstFALSE
  | ConstCustom String
  deriving (Eq, Show) 

data Operation =
    Plus 
  | Minus
  | Mult
  | Div
  | Abs
  | Sqrt
  | Cbrt
  | Pow
  | Exp
  | Log
  | Sin
  | Cos
  | Tan
  | Eq
  | NEq
  | Lt
  | Gt
  | LtEq
  | GtEq
  | And
  | Or
  | Not
  | CustOp Identifier
  deriving (Eq, Show) 

data Property = Property
  { propKey   :: String
  , propValue :: Expr
  }
  deriving (Eq, Show)
      

data Expr
  = ENumber Number
  | EConst Constant
  | EVar Identifier
  | EOp Operation [Expr]
  | EIf Expr Expr Expr
  | ELet  [(Identifier, Expr)] Expr
  | EArray [Expr]
  | EAnnotate [Property] Expr
  deriving (Eq, Show)

data FPCore = FPCore
  { fpcoreName       :: Maybe Identifier
  , fpcoreParams     :: [Identifier]
  , fpcoreProperties :: [Property]
  , fpcoreBody       :: Expr
  }
  deriving (Eq, Show)  

type FPCoreProg = [FPCore]
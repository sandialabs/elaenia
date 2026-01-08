module Imp.AST 
  (IType (..),
   FuncDecl (..),
   Statement (..),
   Exp (..),
   Op (..)
  ) 
  where

import Lib

data IType =
    TInt
  | TString
  | TChar
  | TBool
  | TFun [IType] IType
  | TVoid
  deriving (Show, Eq)

data FuncDecl a = 
  FuncDecl { position :: a,
             funId :: Ident,
             funArgsTys :: [(Ident,IType)],
             funRetTy :: IType,
             funBody:: [Statement a]
            }
    deriving (Show)


data Statement a = 
    If a (Exp a) [Statement a] [Statement a]
  | VarDecl a IType Ident (Exp a)
  | Ass a Ident (Exp a)
  | Return a (Exp a)
  | SExp a (Exp a)
  | Func (FuncDecl a)
  deriving (Show)

data Exp a = 
    Var a Ident
  | EInt a Int
  | EBool a Bool
  | EAnd a (Exp a) (Exp a)
  | ENot a (Exp a)
  | EString a String
  | EChar a Char
  | Infix a (Exp a) Op (Exp a)
  | FunCall a Ident [Exp a]
  deriving (Show)

data Op =
    Add
  | Sub
  | Mul
  | Div
  | Eq
  deriving (Show)
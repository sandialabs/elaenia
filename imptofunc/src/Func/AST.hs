module Func.AST where

import Lib

data FType =
    TInt
  | TString
  | TChar
  | TBool
  | TTuple (FType, FType)
  | TFun [FType] FType
  | TMaybe FType
  | TStar
  deriving Show

data TLD a = 
     FuncDecl   {funPosition :: a,
                 funId :: Ident,
                 funArgsTys :: [(Ident,FType)],
                 funRetTy :: FType,
                 funBody:: Exp a
                } deriving (Show)

data Lam a = Lam 
                {lamId :: a,
                 lamArgsTys :: [(Ident,FType)],
                 lamRetTy :: FType,
                 lamBody :: (Exp a)
                } deriving Show


data Exp a = 
    Var a Ident
  | Infix a (Exp a) Op (Exp a)
  | EInt a Int
  | EBool a Bool
  | EString a String
  | EIte a (Exp a) (Exp a) (Exp a)
  | ENot a (Exp a)
  | ETuple a ((Exp a), (Exp a))
  | ELet a Ident (Exp a) (Exp a)
  | ELam a (Lam a)
  | EJust a (Exp a)
  | ENothing a
  | FuncCall a (Exp a) [Exp a]
  deriving (Show)

data Op =
    Add
  | Sub
  | Mul
  | Div
  | Eq
  | Or
  | And
  deriving (Show, Eq)
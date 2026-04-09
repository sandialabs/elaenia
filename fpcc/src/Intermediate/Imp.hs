{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
module Intermediate.Imp 
  (IType (..),
   FuncDecl (..),
   Statement (..),
   Exp (..),
   Op (..),
   isRel
  ) 
  where

import Lib

import GHC.Generics (Generic)
import qualified Data.Map as M

type Enums = M.Map Ident [Atom]

type Structs = M.Map Ident [(Ident, IType)]

data StructInst a = StructInst Ident [(Ident,Exp a)]

data IType =
    TInt
  | TString
  | TChar
  | TBool
  | TFloat
  | TDouble
  | TStruct Ident
  | TArray IType Integer
  | TFun [IType] IType
  | TEnum Ident
  | TVector IType Int
  | TVoid
  deriving (Show, Eq)

data FuncDecl a = 
  FuncDecl { position :: a,
             funId :: Ident,
             funArgsTys :: [(Ident,IType)],
             funRetTy :: IType,
             funBody:: [Statement a],
             preConditions :: [Exp a]
            }
    deriving (Show, Functor, Generic)


data Statement a = 
    If a (Exp a) [Statement a] [Statement a]
  | VarDecl a IType Ident (Maybe (Exp a))
  | TypeDecl a Ident [(Ident,IType)]
  | Ass a (Exp a) (Exp a)
  | Return a (Exp a)
  | SExp a (Exp a)
  | Func (FuncDecl a)
  deriving (Show, Functor, Generic)

data Exp a = 
    Var a Ident
  | EInt a Int
  | EDouble a String
  | EFloat a String
  | EBool a Bool
  | EAnd a (Exp a) (Exp a)
  | EOr a (Exp a) (Exp a)
  | EStructAcc a (Exp a) Ident
  | ArrAcc a (Exp a) (Exp a)
  | ENot a (Exp a)
  | EString a String
  | EChar a Char
  | Infix a (Exp a) Op (Exp a)
  | FunCall a Ident [Exp a]
  deriving (Show, Functor, Generic)

data Op =
    Add
  | Sub
  | Mul
  | Div
  | Eq
  | Gt
  | Lt
  | Neq
  | LtEq
  deriving (Show)

isRel :: Op -> Bool  
isRel Neq = True
isRel LtEq = True
isRel Gt = True
isRel Lt = True
isRel _ = False
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

instance Eq (Statement a) where
  s1 == s2 = case (s1, s2) of
    (If _ e1 t1 f1,       If _ e2 t2 f2)       -> (e1,t1,f1) == (e2,t2,f2)
    (VarDecl _ t1 i1 e1,  VarDecl _ t2 i2 e2)  -> (t1,i1,e1) == (t2,i2,e2)
    (TypeDecl _ i1 fs1,   TypeDecl _ i2 fs2)   -> (i1,fs1)   == (i2,fs2)
    (Ass _ l1 r1,         Ass _ l2 r2)         -> (l1,r1)    == (l2,r2)
    (Return _ e1,         Return _ e2)         -> e1 == e2
    (SExp _ e1,           SExp _ e2)           -> e1 == e2
    _                                             -> False  


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
  | EUnOp a Op (Exp a)
  | Infix a (Exp a) Op (Exp a)
  | FunCall a Ident [Exp a]
  deriving (Show, Functor, Generic)

instance Eq (Exp a) where
  x == y = case (x, y) of
    (Var _ i,           Var _ j)           -> i == j
    (EInt _ i,          EInt _ j)          -> i == j
    (EDouble _ s,       EDouble _ t)       -> s == t
    (EFloat _ s,        EFloat _ t)        -> s == t
    (EBool _ b,         EBool _ c)         -> b == c
    (EAnd _ a b,        EAnd _ c d)        -> a == c && b == d
    (EOr _ a b,         EOr _ c d)         -> a == c && b == d
    (EStructAcc _ e i,  EStructAcc _ f j)  -> e == f && i == j
    (ArrAcc _ a i,      ArrAcc _ b j)      -> a == b && i == j
    (ENot _ e,          ENot _ f)          -> e == f
    (EString _ s,       EString _ t)       -> s == t
    (EChar _ c,         EChar _ d)         -> c == d
    (EUnOp _ op e,      EUnOp _ op' e')    -> op == op' && e == e'
    (Infix _ l op r,    Infix _ l' op' r') -> op == op' && l == l' && r == r'
    (FunCall _ f xs,    FunCall _ g ys)    -> f == g && xs == ys
    _                                      -> False  

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
  deriving (Eq, Show)

isRel :: Op -> Bool  
isRel Neq = True
isRel LtEq = True
isRel Gt = True
isRel Lt = True
isRel _ = False
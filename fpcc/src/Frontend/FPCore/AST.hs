module Frontend.FPCore.AST (
  Pred (..),
  Term (..),
  CmpOp (..),
  ArithOp (..),
) where

import Lib (Ident)

data Pred a
  = And a [Pred a]
  | Or a [Pred a]
  | Not a (Pred a)
  | Compare a CmpOp [Term a]
  deriving (Eq, Show)

data Term a
  = Num a Rational
  | Var a Ident
  | Op a ArithOp [Term a]
  deriving (Eq, Show)

data CmpOp
  = Lt
  | Le
  | Gt
  | Ge
  | Eq
  | Neq
  deriving (Eq, Show)

data ArithOp
  = Add
  | Sub
  | Mul
  | Div
  deriving (Eq, Show)

instance Functor Pred where
  fmap f (And a ps) = And (f a) (map (fmap f) ps)
  fmap f (Or a ps) = Or (f a) (map (fmap f) ps)
  fmap f (Not a p) = Not (f a) (fmap f p)
  fmap f (Compare a op ts) = Compare (f a) op (map (fmap f) ts)

instance Functor Term where
  fmap f (Num a r) = Num (f a) r
  fmap f (Var a x) = Var (f a) x
  fmap f (Op a op ts) = Op (f a) op (map (fmap f) ts)

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE OverloadedRecordDot #-}
module Intermediate.Func where

import Data.Maybe (catMaybes)
import Data.Generics.Uniplate.Data (universe)
import Data.Data (Data, Typeable)

import Lib

data FType =
    TInt
  | TFloat
  | TDouble
  | TString
  | TChar
  | TBool
  | TSyn Ident FType
  | TRecord [(Ident, FType)]
  | TVector FType Integer
  | TTuple (FType, FType)
  | TFun [FType] FType
  | TMaybe FType
  | TStar
  deriving (Show, Eq, Data, Typeable)


vectorType :: FType -> Maybe FType
vectorType (TVector ty _)          = Just ty
vectorType (TSyn _ (TVector ty _)) = Just ty
vectorType _ = Nothing


data FuncDecl a =
  FuncDecl {funPosition :: a,
            funId :: Ident,
            funArgsTys :: [(Ident,FType)],
            funRetTy :: FType,
            funBody:: Exp a,
            funPreconds :: [Exp a]
           } deriving (Show)

funTy :: FuncDecl a -> FType
funTy fDecl = TFun (snd <$> funArgsTys fDecl) (funRetTy fDecl)

data TLD a = TLFuncDecl (FuncDecl a) | TLTypeSyn a Ident FType
  deriving (Show)

type FuncProg a = [TLD a]  

funDecl :: forall a. a -> Ident -> [(Ident,FType)] -> FType -> Exp a -> [Exp a] -> TLD a
funDecl pos id' argDecls retTy body preconds =
  TLFuncDecl $ FuncDecl
    { funPosition = pos,
      funId = id',
      funArgsTys = argDecls,
      funRetTy = retTy,
      funBody = body,
      funPreconds = preconds
    }

data Lam a = Lam
                {lamId :: a,
                 lamArgsTys :: [(Ident,FType)],
                 lamRetTy :: FType,
                 lamBody :: Exp a
                } deriving (Show, Data, Typeable, Functor)


data Exp a =
    Var a Ident FType
  | Infix a (Exp a) Op (Exp a)
  | ECompRel a (Exp a) Op (Exp a) Op (Exp a)
  | EInt a Int
  | EFloat a String
  | EDouble a String
  | EBool a Bool
  | EChar a Char
  | ERec a [(Ident, Exp a)]
  | EVec a [Exp a]
  | ERecRead a Ident (Exp a)
  | ERecWrite a Ident (Exp a) (Exp a)
  | EVecRead a Ident FType (Exp a)
  | EVecWrite a Ident FType (Exp a) (Exp a)
  | EString a String
  | EIte a (Exp a) (Exp a) (Exp a)
  | ENot a (Exp a)
  | ETuple a (Exp a, Exp a)
  | ELet a Ident FType (Exp a) (Exp a)
  | ELam a (Lam a)
  | EJust a (Exp a)
  | ENothing a
  | FuncCall a (Exp a) [Exp a]
  deriving (Show, Data, Typeable, Functor)

data Op =
    Add
  | Sub
  | Mul
  | Div
  | Eq
  | Or
  | And
  | Neq
  | Lt
  | LtEq
  | Gt
  deriving (Show, Eq, Data, Typeable)


typeOf :: Exp a -> Maybe FType
typeOf (Var _ _ ty) = Just ty
typeOf (EFloat {}) = Just TFloat
typeOf (EDouble {}) = Just TDouble
typeOf (EBool {}) = Just TBool
typeOf (EChar {}) = Just TChar
typeOf (EString {}) = Just TString
typeOf (ELam _ lam) = Just $ typeOfLam lam
typeOf (EVecRead _ _ ty _) = Just ty
typeOf _ = Nothing

typeOfLam :: Lam a -> FType
typeOfLam lam = TFun (snd <$> lamArgsTys lam) lam.lamRetTy

binOpType :: Exp () -> Maybe FType
binOpType e = allEqualMaybe $ map typeOf (subExprs e)
  where
    subExprs :: Exp () -> [Exp ()]
    subExprs = universe
    allEqualMaybe :: Eq a => [Maybe a] -> Maybe a
    allEqualMaybe xs =
      case catMaybes xs of
        []     -> Nothing
        y : ys -> if all (== y) ys then Just y else Nothing
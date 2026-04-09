{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE InstanceSigs #-}
module Intermediate.PrettyPrinter (PP, pp) where

import Data.List ( intercalate )
import Intermediate.Func
import Text.Printf
import Lib


instance PP [(Ident, FType)] where
  pp flds = intercalate "," (map (\(id',ty) -> printf "(%s:%s)" id' (pp ty)) flds)


instance PP FType where
  pp TInt = "int"
  pp TFloat = "float"
  pp TDouble = "double"
  pp (TSyn name _) = name
  pp TString = "string"
  pp TChar = "char"
  pp TBool = "bool"
  pp (TVector ty size) = pp ty ++ printf " vector<%s>" (show size)
  pp (TRecord flds) = "record : " ++ pp flds
  pp (TTuple (t1,t2)) = printf "(%s,%s)" (pp t1) (pp t2)
  pp (TFun args ret) = ppParens $ intercalate " -> " (map pp (args ++ [ret]))
  pp (TMaybe t) = printf "maybe %s" (pp t)
  pp TStar = "*"

ppParens :: String -> String
ppParens s = "(" ++ s ++ ")"

instance PP (Lam a) where
  pp lam =
    printf "(fun %s: %s -> %s)"
      (ppArgsTys (lamArgsTys lam))
      (pp (lamRetTy lam))
      (pp (lamBody lam))


instance PP (TLD a) where
  pp (TLFuncDecl fDecl) =
    ppPreConds (funPreconds fDecl)
    ++
    printf "%s %s: %s = %s;\n"
      (funId fDecl)
      (ppArgsTys (funArgsTys fDecl))
      (pp (funRetTy fDecl))
      (pp (funBody fDecl))
  pp (TLTypeSyn _ id' ty) =
    printf "type %s = %s;" id' (pp ty)

ppPreConds :: [Exp a] -> String
ppPreConds = \case
  [] -> ""
  precs -> "/*@\n" ++ concatMap require precs ++ "*/\n"
    where
      require e = printf "\trequires %s;\n" (pp e)

instance PP [TLD a] where
  pp funDecls = intercalate "\n" (map pp funDecls)

ppArgsTys :: [(Ident,FType)] -> String
ppArgsTys argsTys = unwords args
  where
    args = map (\(i,t) -> printf "(%s:%s)" i (pp t)) argsTys

instance PP (Exp a) where
  pp :: Exp a -> String
  pp (Var _ i _) = i
  pp (Infix _ e1 op e2) = ppParens $ concat [pp e1, pp op, pp e2]
  pp (EInt _ i) = show i
  pp (EFloat _ f) = f
  pp (EDouble _ f) = f
  pp (EChar _ c) = show c
  pp (EBool _ True) = "true"
  pp (EBool _ False) = "false"
  pp (EString _ s) = ppQuotes s
  pp (EVecRead _ vecId _ ix) = vecId ++ printf "[%s]" (pp ix)
  pp (EVecWrite _ vecId _ ix val) = vecId ++ printf "[%s |-> %s]" (pp ix) (pp val)
  pp (EVec _ xs) = printf "[%s]" (intercalate "," $ map pp xs)
  pp (ERecRead _ recId fld) = show recId ++ printf "->%s" (pp fld)
  pp (EIte _ p t e) =
    printf "if (%s) then %s else %s" (pp p) (pp t) (pp e)
  pp (ENot _ e) = printf "!%s" (pp e)
  pp (ETuple _ (l,r)) = printf "(%s,%s)" (pp l) (pp r)
  pp (ELet _ i _ b e) = printf "let %s = %s in\
                             \ %s" i (pp b) (pp e)
  pp (ELam _ lam) = pp lam
  pp (EJust _ e) = printf "Just(%s)" (pp e)
  pp (ENothing _) = "Nothing"
  pp (FuncCall _ f args) = printf "%s(%s)" (pp f) (intercalate "," (map pp args))
  pp _ = undefined

ppQuotes :: String -> String
ppQuotes s = "\"" ++ s ++ "\""

instance PP Op where
  pp Add = "+"
  pp Sub = "-"
  pp Mul = "*"
  pp Div = "/"
  pp Eq = "=="
  pp Or = "||"
  pp And = "&&"
  pp Neq = "/="
  pp LtEq = "<="
  pp Gt = ">"

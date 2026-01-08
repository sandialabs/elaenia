{-# LANGUAGE FlexibleInstances #-}
module Func.PrettyPrinter where

import Data.List
import Func.AST
import Text.Printf
import Func.Parser
import Lib


class PP a where
  pp :: a -> String

instance PP FType where
  pp TInt = "int"
  pp TString = "string"
  pp TChar = "char"
  pp TBool = "bool"
  pp (TTuple (t1,t2)) = printf "(%s,%s)" (pp t1) (pp t2)
  pp (TFun args ret) = ppParens $ intercalate " -> "(map pp (args ++ [ret]))
  pp (TMaybe t) = printf "maybe %s" (pp t)
  pp (TStar) = "*"

ppParens :: String -> String  
ppParens s = "(" ++ s ++ ")"

instance PP (Lam a) where
  pp lam = 
    printf "(fun %s: %s -> %s)" 
      (ppArgsTys (lamArgsTys lam)) 
      (pp (lamRetTy lam)) 
      (pp (lamBody lam))


instance PP (TLD a) where
  pp funDecl =
    printf "%s %s: %s = %s;\n" 
      (funId funDecl) 
      (ppArgsTys (funArgsTys funDecl)) 
      (pp (funRetTy funDecl))
      (pp (funBody funDecl))

instance PP [TLD a] where
  pp funDecls = concatMap pp funDecls

ppArgsTys :: [(Ident,FType)] -> String
ppArgsTys argsTys = intercalate " " args
  where
    args = map (\(i,t) -> printf "(%s:%s)" i (pp t)) argsTys

instance PP (Exp a) where
  pp (Var _ i) = i
  pp (Infix _ e1 op e2) = ppParens $ concat [pp e1, pp op, ppParens (pp e2)]
  pp (EInt _ i) = show i
  pp (EBool _ True) = "true"
  pp (EBool _ False) = "false"
  pp (EString _ s) = ppQuotes s
  pp (EIte _ p t e) = 
    printf "if (%s) then %s else %s" (pp p) (pp t) (pp e)
  pp (ENot _ e) = printf "!%s" (pp e)
  pp (ETuple _ (l,r)) = printf "(%s,%s)" (pp l) (pp r)
  pp (ELet _ i b e) = printf "let %s = %s in\
                             \ %s" i (pp b) (pp e)
  pp (ELam _ lam) = pp lam
  pp (EJust _ e) = printf "Just(%s)" (pp e)
  pp (ENothing _) = "Nothing"
  pp (FuncCall _ f args) = printf "%s(%s)" (pp f) (intercalate "," (map pp args))

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

ppInput :: FilePath -> IO ()
ppInput path = do
  res <- parseFunc path
  case res of
    Left err -> error (show err)
    Right tlds -> writeFile "input-pp.func" (concatMap pp tlds)
module Frontend.FPCore.ToACSL (
  toAcslComment,
  acslCommentLines,
  acslRequires,
  acslPred,
  acslTerm,
  acslReal,
) where

import Data.List (intercalate, tails)
import Data.Ratio (denominator, numerator)
import Frontend.FPCore.AST (ArithOp (..), CmpOp (..), Pred (..), Term (..))

toAcslComment :: Pred a -> String
toAcslComment = unlines . acslCommentLines

acslCommentLines :: Pred a -> [String]
acslCommentLines p =
  ["/*@"] ++ map (\r -> "  requires " ++ r ++ ";") (acslRequires p) ++ ["*/"]

acslRequires :: Pred a -> [String]
acslRequires (And _ ps) = concatMap acslRequires ps
acslRequires p = [acslPred p]

acslPred :: Pred a -> String
acslPred (And _ ps) = "(" ++ intercalate " && " (map acslPred ps) ++ ")"
acslPred (Or _ ps) = "(" ++ intercalate " || " (map acslPred ps) ++ ")"
acslPred (Not _ p) = "!(" ++ acslPred p ++ ")"
acslPred (Compare _ op ts)
  | op == Eq = intercalate " && " $ map (uncurry comparison) (adjacentPairs ts)
  | op == Neq = intercalate " && " $ map (uncurry comparison) (distinctPairs ts)
  | otherwise = intercalate (" " ++ acslSymbol op ++ " ") (map acslTerm ts)
  where
    adjacentPairs xs = zip xs (tail xs)
    distinctPairs xs = [(a, b) | (a : rest) <- tails xs, b <- rest]
    comparison a b = acslTerm a ++ " " ++ acslSymbol op ++ " " ++ acslTerm b

acslTerm :: Term a -> String
acslTerm (Num _ r) = acslReal r
acslTerm (Var _ x) = x
acslTerm (Op _ Sub [t]) = "-" ++ acslTerm t
acslTerm (Op _ op ts) = "(" ++ intercalate (" " ++ acslSymbol op ++ " ") (map acslTerm ts) ++ ")"

acslReal :: Rational -> String
acslReal r
  | denominator r == 1 = show (numerator r)
  -- PRECiSA converts bounds to doubles internally, so there's no point trying
  -- to preserve more precision here.
  | otherwise = show (fromRational r :: Double)

class ACSLSymbol a where
  acslSymbol :: a -> String

instance ACSLSymbol CmpOp where
  acslSymbol Lt = "<"
  acslSymbol Le = "<="
  acslSymbol Gt = ">"
  acslSymbol Ge = ">="
  acslSymbol Eq = "=="
  acslSymbol Neq = "!="

instance ACSLSymbol ArithOp where
  acslSymbol Add = "+"
  acslSymbol Sub = "-"
  acslSymbol Mul = "*"
  acslSymbol Div = "/"

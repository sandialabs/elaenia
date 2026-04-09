{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Backend.FPCore.Pretty
  ( prettyFPCoreProg
  , prettyFPCore
  , prettyExpr
  , prettyProperty
  ) where

import Backend.FPCore.AST
import Data.List (intersperse)
import qualified Data.Text as T
import Prettyprinter
  ( Doc, Pretty(..)
  , align, brackets, comma, group
  , hang, hsep, line, parens, punctuate, sep
  , vsep, (<+>)
  )


prettyFPCoreProg :: FPCoreProg -> Doc ann
prettyFPCoreProg = vsep . intersperse line . map prettyFPCore

prettyFPCore :: FPCore -> Doc ann
prettyFPCore (FPCore mname params props body) =
  group $
    parens $
      hang 2 $
        vsep $
          header : map prettyProperty props ++ [prettyExpr body]
  where
    header =
      hsep $
        [ "FPCore"
        ]
        ++ maybe [] (\nm -> [prettyIdent nm]) mname
        ++ [parens (hsep (map prettyIdent params))]

prettyProperty :: Property -> Doc ann
prettyProperty (Property k v) =
  prettyPropKey k <+> prettyExpr v


prettyExpr :: Expr -> Doc ann
prettyExpr = \case
  ENumber n      -> prettyNumber n
  EConst c       -> prettyConstant c
  EVar x         -> prettyIdent x
  EOp op args    -> parens (prettyOperation op <+> align (sep (map prettyExpr args)))
  EIf c t e      -> parens ("if" <+> prettyExpr c <+> prettyExpr t <+> prettyExpr e)
  ELet bs body   ->
    parens $
      hang 2 $
        vsep
          [ "let"
          , parens (align (vsep (map prettyBinding bs)))
          , prettyExpr body
          ]
  EArray es      -> brackets (align (sep (punctuate comma (map prettyExpr es))))
  EAnnotate ps e ->
    parens $
      hang 2 $
        vsep $
          "!" : map prettyProperty ps ++ [prettyExpr e]


prettyBinding :: (Identifier, Expr) -> Doc ann
prettyBinding (x, e) = parens (prettyIdent x <+> prettyExpr e)


prettyIdent :: Identifier -> Doc ann
prettyIdent = pretty . T.pack

prettyPropKey :: String -> Doc ann
prettyPropKey k =
  case k of
    (':':_) -> pretty (T.pack k)
    _       -> pretty (T.pack (':' : k))

prettyNumber :: Number -> Doc ann
prettyNumber = \case
  NumInteger i  -> pretty i
  NumDecimal s  -> pretty (T.pack s)


prettyConstant :: Constant -> Doc ann
prettyConstant = \case
  ConstE           -> "E"
  ConstLOG2E       -> "LOG2E"
  ConstLOG10E      -> "LOG10E"
  ConstLN2         -> "LN2"
  ConstLN10        -> "LN10"
  ConstPI          -> "PI"
  ConstPI_2        -> "PI_2"
  ConstPI_4        -> "PI_4"
  ConstM_1_PI      -> "M_1_PI"
  ConstM_2_PI      -> "M_2_PI"
  ConstM_2_SQRTPI  -> "M_2_SQRTPI"
  ConstSQRT2       -> "SQRT2"
  ConstSQRT1_2     -> "SQRT1_2"
  ConstINFINITY    -> "INFINITY"
  ConstNAN         -> "NAN"
  ConstTRUE        -> "TRUE"
  ConstFALSE       -> "FALSE"
  ConstCustom s    -> pretty (T.pack s)

prettyOperation :: Operation -> Doc ann
prettyOperation = \case
  Plus    -> "+"
  Minus   -> "-"
  Mult    -> "*"
  Div     -> "/"
  Abs     -> "abs"
  Sqrt    -> "sqrt"
  Cbrt    -> "cbrt"
  Pow     -> "pow"
  Exp     -> "exp"
  Log     -> "log"
  Sin     -> "sin"
  Cos     -> "cos"
  Tan     -> "tan"
  Eq      -> "=="
  NEq     -> "!="
  Lt      -> "<"
  Gt      -> ">"
  LtEq    -> "<="
  GtEq    -> ">="
  And     -> "and"
  Or      -> "or"
  Not     -> "not"
  CustOp f -> prettyIdent f

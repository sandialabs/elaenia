module Intermediate.ImpPretty
  ( ppIType
  , ppOp
  , ppExp
  , ppStmt
  , ppFuncDecl
  , ppProgram
  ) where

import Intermediate.Imp
import Lib (Ident)

import Data.List (intercalate)


ppIdent :: Ident -> String
ppIdent = show


indent :: Int -> String
indent n = replicate (2*n) ' '

parensIf :: Bool -> String -> String
parensIf True  s = "(" ++ s ++ ")"
parensIf False s = s

commaSep :: [String] -> String
commaSep = intercalate ", "

semi :: String -> String
semi s = s ++ ";"

block :: Int -> [String] -> String
block k ss =
  "{\n" ++ unlines (map (indent (k+1) ++) ss) ++ indent k ++ "}"


ppIType :: IType -> String
ppIType TInt             = "int"
ppIType TString          = "string"
ppIType TChar            = "char"
ppIType TBool            = "bool"
ppIType TFloat           = "float"
ppIType TDouble          = "double"
ppIType (TStruct x)      = "struct " ++ ppIdent x
ppIType (TArray t n)     = ppIType t ++ "[" ++ show n ++ "]"
ppIType (TFun as r)      = "fun(" ++ commaSep (map ppIType as) ++ ") -> " ++ ppIType r
ppIType (TEnum x)        = "enum " ++ ppIdent x
ppIType (TVector t n)    = "vector<" ++ ppIType t ++ "," ++ show n ++ ">"
ppIType TVoid            = "void"

ppOp :: Op -> String
ppOp Add  = "+"
ppOp Sub  = "-"
ppOp Mul  = "*"
ppOp Div  = "/"
ppOp Eq   = "=="
ppOp Gt   = ">"
ppOp Lt   = "<"
ppOp Neq  = "!="
ppOp LtEq = "<="


-- higher = binds tighter
precExp :: Exp a -> Int
precExp e = case e of
  EOr{}        -> 2
  EAnd{}       -> 3
  Infix _ _ op _ | isRel op -> 4
  Infix{}      -> 6            -- +,-,*,/ (we'll refine below)
  EUnOp{}      -> 8
  ENot{}       -> 8
  EStructAcc{} -> 9
  ArrAcc{}     -> 9
  FunCall{}    -> 9
  _            -> 10

precOp :: Op -> Int
precOp Add  = 6
precOp Sub  = 6
precOp Mul  = 7
precOp Div  = 7
precOp Eq   = 4
precOp Gt   = 4
precOp Lt   = 4
precOp Neq  = 4
precOp LtEq = 4

ppExp :: Exp a -> String
ppExp = ppExpP 0

ppExpP :: Int -> Exp a -> String
ppExpP ctx e =
  let p = precExp e
      out = case e of
        Var _ x           -> ppIdent x
        EInt _ n          -> show n
        EDouble _ s       -> s
        EFloat _ s        -> s
        EBool _ b         -> if b then "true" else "false"
        EString _ s       -> show s         -- Haskell-style quoted string
        EChar _ c         -> show c         -- Haskell-style quoted char

        ENot _ e1         -> "!" ++ ppExpP p e1
        EUnOp _ op e1     -> ppOp op ++ ppExpP p e1

        EAnd _ a b        -> bin 3 "&&" a b
        EOr  _ a b        -> bin 2 "||" a b

        Infix _ a op b    ->
          let opP = precOp op
          in parensIf (ctx > opP) (ppExpP opP a ++ " " ++ ppOp op ++ " " ++ ppExpP (opP+1) b)

        FunCall _ f args  -> ppIdent f ++ "(" ++ commaSep (map ppExp args) ++ ")"
        EStructAcc _ e1 fld -> ppExpP 9 e1 ++ "." ++ ppIdent fld
        ArrAcc _ a i      -> ppExpP 9 a ++ "[" ++ ppExp i ++ "]"
      in parensIf (ctx > p) out
  where
    bin :: Int -> String -> Exp a -> Exp a -> String
    bin p op a b = parensIf (ctx > p) (ppExpP p a ++ " " ++ op ++ " " ++ ppExpP (p+1) b)

-- ------------------------------------------------------------
-- Statements / functions
-- ------------------------------------------------------------

ppStmt :: Statement a -> String
ppStmt = ppStmtI 0

ppStmtI :: Int -> Statement a -> String
ppStmtI k st = case st of
  If _ c th el ->
    "if (" ++ ppExp c ++ ") "
      ++ block k (map (ppStmtI (k+1)) th)
      ++ (if null el then "" else " else " ++ block k (map (ppStmtI (k+1)) el))

  VarDecl _ ty x Nothing  ->
    semi (ppIType ty ++ " " ++ ppIdent x)

  VarDecl _ ty x (Just e) ->
    semi (ppIType ty ++ " " ++ ppIdent x ++ " = " ++ ppExp e)

  TypeDecl _ name fields ->
    "type " ++ ppIdent name ++ " "
      ++ block k [ semi (ppIType ty ++ " " ++ ppIdent f) | (f,ty) <- fields ]

  Ass _ lhs rhs ->
    semi (ppExp lhs ++ " = " ++ ppExp rhs)

  Return _ e ->
    semi ("return " ++ ppExp e)

  SExp _ e ->
    semi (ppExp e)

  Func fd ->
    ppFuncDeclI k fd

ppFuncDecl :: FuncDecl a -> String
ppFuncDecl = ppFuncDeclI 0

ppFuncDeclI :: Int -> FuncDecl a -> String
ppFuncDeclI k (FuncDecl _ fid args ret body pres) =
  let header =
        ppIType ret ++ " " ++ ppIdent fid
          ++ "("
          ++ commaSep [ ppIType ty ++ " " ++ ppIdent x | (x,ty) <- args ]
          ++ ")"
      preLines =
        [ semi ("requires " ++ ppExp p) | p <- pres ]
      bodyLines =
        preLines ++ map (ppStmtI (k+1)) body
  in header ++ " " ++ block k bodyLines

-- Program = list of top-level statements (often just Func/TypeDecl/VarDecl)
ppProgram :: [Statement a] -> String
ppProgram sts = unlines (map ppStmt sts)
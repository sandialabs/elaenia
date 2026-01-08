module Func.Parser (parseFunc) where

import Text.Parsec
import Text.Parsec.Char
import Text.Parsec.Prim
import Prelude hiding (exp)
import Text.Parsec.Pos (SourcePos)

import Lib
import qualified Func.AST as AST
import Func.AST hiding (Exp,TLD,Lam)

type Exp = AST.Exp SourcePos
type TLD = AST.TLD SourcePos
type Lam = AST.Lam SourcePos

pos :: (SourcePos -> b) -> Parser b
pos c = c <$> getPosition  

type Parser = Parsec String ()

ident :: Parser Ident
ident = many1 letter <> many alphaNum

integer :: Parser Int
integer = read <$> ((optional $ char '-') *> (many1 digit))

parens :: Parser a -> Parser a
parens = between (char '(') (char ')')

op :: Parser Op
op =
  Add <$ char '+' <|>
  Sub <$ char '-' <|>
  Mul <$ char '*' <|>
  Div <$ char '/' <|>
  Eq <$ string "==" <|>
  Or <$ string "||" <|>
  And <$ string "&&"

funType :: Parser FType  
funType = do
  tys <- parens $ atomicType `sepBy1` (string " -> ")
  return $ TFun (init tys) (head . reverse $ tys)

atomicType :: Parser FType
atomicType = 
  string "int" *> pure TInt <|>
  string "string" *> pure TString <|>
  string "char" *> pure TChar <|>
  string "bool" *> pure TBool <|>
  string "*" *> pure TStar <|>
  TMaybe <$> (string "maybe " *> atomicType)

tupleType :: Parser FType  
tupleType = TTuple <$> parens ((,) <$> atomicType <* char ',' <*> (atomicType <|> ftype))

ftype :: Parser FType
ftype = 
  try tupleType <|>
  try funType <|>
  atomicType



paramList :: Parser [(Ident,FType)]
paramList = param `sepBy` space
  where
    param = parens $ (,) <$> (ident <* char ':') <*> ftype


tld :: Parser TLD
tld = comments $
    pos FuncDecl <*> 
        (ident <* space) <*> 
        (paramList <* string ": ") <*> 
        ftype <*> (string " = " *> trim (exp <* semi))
  where
    trim = between (many whitespace) (many whitespace)
    semi = char ';'
    comment = ((string "/*") *> anyChar `manyTill` (try $ string "*/"))
    comments = between (many comment) (many comment)

whitespace :: Parser Char
whitespace = char ' ' <|> char '\n' <|> char '\t'


funcCall :: Parser Exp
funcCall = (pos FuncCall) <*> exp' <*> parens argList
  where
    exp' = 
      (pos ELam <*> lam) <|>
      (pos Var) <*> ident


argList :: Parser [Exp]
argList = (exp  <* notFollowedBy res) `sepBy` (char ',')
  where
    reserved = [" in", " then", " else", " ->"]
    res = choice $ map string reserved

elet :: Parser Exp
elet = do
    try $ string "let "
    ident <- ident
    string " = "
    e1 <- exp
    string " in" <* many whitespace
    e2 <- exp
    p <- getPosition
    return $ ELet p ident e1 e2

eite :: Parser Exp
eite = do
  try (string "if ")
  predicate <- exp
  string " then "
  then' <- exp
  string " else "
  else' <- exp
  p <- getPosition
  return $ EIte p predicate then' else'
  
lam :: Parser Lam
lam = do
  (try $ string "(fun ")
  params <- paramList
  ty <- string ": " *> ftype
  string " -> "
  body <- exp <* char ')'
  p <- getPosition
  return $ AST.Lam p params ty body

tuple :: Parser Exp
tuple = (pos ETuple) <*> parens ((,) <$> exp <* char ',' <*> exp)

exp :: Parser Exp
exp = try (parens exp') <|> exp'
  where 
    exp' =
      elet <|>
      eite <|>
      ((pos EString) <*> quoted (many alphaNum)) <|>
      (pos ELam <*> lam) <|>
      (pos ENot <*> (string "!" *> exp)) <|>
      try tuple <|>
      parens ((pos Infix) <*> exp <*> op <*> exp) <|>
      try ((pos EBool) <*> (string "true" *> pure True <|> string "false" *> pure False)) <|>
      (pos EInt) <*> integer <|>
      string "Nothing" *> (pos ENothing) <|>
      (pos EJust) <*> (string "Just" *> parens exp) <|>
      try funcCall <|>
      (pos Var) <*> ident

quoted :: Parser String -> Parser String
quoted = between (char '"') (char '"')

tlds :: Parser [TLD]
tlds = many1 tld

parseFunc :: FilePath -> IO (Either ParseError [TLD])
parseFunc filePath = do
  src <- readFile filePath
  return $ (runParser tlds () filePath src)
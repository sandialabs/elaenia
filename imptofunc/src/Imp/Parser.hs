module Imp.Parser (parseImp) where

import Text.Parsec
import Text.Parsec.Char
import Prelude hiding (exp, sequence)

import Lib
import Imp.AST hiding (Exp, Statement)
import qualified Imp.AST as AST

type Exp = AST.Exp SourcePos
type Statement = AST.Statement SourcePos


type Parser = Parsec String ()

pos :: (SourcePos -> b) -> Parser b
pos c = c <$> getPosition  

ident :: Parser Ident
ident = many1 letter <> many alphaNum

itype :: Parser IType
itype = 
  string "int" *> pure TInt <|>
  string "string" *> pure TString <|>
  string "char" *> pure TChar <|>
  string "bool" *> pure TBool <|>
  string "void" *> pure TVoid

op :: Parser Op
op =
  Add <$ char '+' <|>
  Sub <$ char '-' <|>
  Mul <$ char '*' <|>
  Div <$ char '/' <|>
  Eq <$ string "=="

exp :: Parser Exp
exp = pos EString <*> ((char '"') *> anyChar `manyTill` (try $ (char '"'))) <|>
      pos EChar <*> between (char '\'') (char '\'') anyChar <|>
      try (pos FunCall <*> ident <*> argList) <|>
      parens (pos Infix <*> exp <*> op <*> exp) <|>
      try (pos EBool <*> (string "true" *> pure True <|> string "false" *> pure False)) <|>
      pos EInt <*> integer <|>
      pos Var <*> ident

integer :: Parser Int
integer = read <$> (many1 digit)
  

argList :: Parser [Exp]
argList = (parens $ exp `sepBy` (char ','))

sequence :: Parser a -> Parser [a]
sequence p = comments ((p `sepEndBy` (char ';' <* whitespaces)) <* whitespaces)
  where
    comment = ((string "/*") *> anyChar `manyTill` (try $ string "*/"))
    comments = between (many comment) (many comment)

funDecl :: Parser Statement
funDecl = do
  _ <- string "function "
  id' <- ident
  params <- paramList
  _ <- char ':'
  retType <- itype
  _ <- string "="
  block <- block Nothing
  pos <- getPosition
  return $ Func $ FuncDecl pos id' params retType block


paramList :: Parser [(Ident,IType)]
paramList = parens $ param `sepBy` (char ',')
  where
    param = (,) <$> (ident <* char ':') <*> itype


tld :: Parser Statement
tld = 
  funDecl <|>
  pos VarDecl <*> (itype <* (char ' ')) <*> (ident <* (string " = ")) <*> exp <|>
  (pos Ass <*> (ident <* (string " = ")) <*> exp)

if' :: Parser Statement
if' = do
  (try $ string "if")
  (pos If <*> (parens exp) <*> block Nothing <*> block (Just "else"))


statement :: Parser Statement
statement =
  if'  <|>
  try (pos VarDecl <*> (itype <* (char ' ')) <*> (ident <* (string " = ")) <*> exp) <|>
  try (pos Ass <*> (ident <* (string " = ")) <*> exp) <|>
  pos Return <*> (string "return " *> exp) <|>
  pos SExp <*> exp


whitespaces :: Parser [Char]
whitespaces = many (char '\n' <|> space)

block :: Maybe String -> Parser [Statement]
block label = case label of
  Nothing -> curlys $ sequence statement
  Just l  -> string l *> (curlys $ sequence statement)
  where
    curlys = between (char '{' <* whitespaces) (char '}')

parens :: Parser a -> Parser a
parens = between (char '(') (char ')')

parseImp :: FilePath -> IO (Either ParseError [Statement])
parseImp filePath = do
  src <- readFile filePath
  return $ (runParser (sequence tld) () filePath src)

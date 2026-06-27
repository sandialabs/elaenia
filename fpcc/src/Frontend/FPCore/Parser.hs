module Frontend.FPCore.Parser (
  Parser,
  parsePredicate,
  preDirective,
  predicate,
  term,
) where

import Frontend.FPCore.AST (ArithOp (..), CmpOp (..), Pred (..), Term (..))
import Frontend.FPCore.Lexer (Token (..), TokenKind (..))
import Lib (Ident)
import Text.Parsec (Parsec, SourcePos, between, choice, eof, many, token, (<?>), (<|>))

type Parser = Parsec [Token SourcePos] ()

parsePredicate :: Parser (Pred SourcePos)
parsePredicate = predicate <* eof

preDirective :: Parser (Pred SourcePos)
preDirective = kind (TPropertyLabel "pre") *> predicate <* eof

predicate :: Parser (Pred SourcePos)
predicate = parens predInner <?> "predicate"
  where
    predInner =
      choice
        [ And <$> kind TAnd <*> many predicate
        , Or <$> kind TOr <*> many predicate
        , Not <$> kind TNot <*> predicate
        , uncurry Compare <$> cmpOp <*> many term
        ]

term :: Parser (Term SourcePos)
term =
  choice
    [ uncurry Num <$> number
    , uncurry Var <$> symbol
    , parens (uncurry Op <$> arithOp <*> many term)
    ]
    <?> "term"

parens :: Parser a -> Parser a
parens p =
  between (kind TLeftParen) (kind TRightParen) p
    <|> between (kind TLeftBracket) (kind TRightBracket) p

satisfyToken :: (TokenKind -> Maybe b) -> Parser (SourcePos, b)
satisfyToken f = token showToken positionToken testToken
  where
    showToken (Token _ k) = show k
    positionToken (Token p _) = p
    testToken (Token p k) = (,) p <$> f k

kind :: TokenKind -> Parser SourcePos
kind k = fst <$> satisfyToken f
  where
    f :: TokenKind -> Maybe ()
    f k'
      | k == k' = Just ()
      | otherwise = Nothing

number :: Parser (SourcePos, Rational)
number = satisfyToken numberValue
  where
    numberValue (TNumber r) = Just r
    numberValue _ = Nothing

symbol :: Parser (SourcePos, Ident)
symbol = satisfyToken symbolName
  where
    symbolName (TSymbol s) = Just s
    symbolName _ = Nothing

cmpOp :: Parser (SourcePos, CmpOp)
cmpOp = satisfyToken c
  where
    c TLt = Just Lt
    c TLe = Just Le
    c TGt = Just Gt
    c TGe = Just Ge
    c TEq = Just Eq
    c TNeq = Just Neq
    c _ = Nothing

arithOp :: Parser (SourcePos, ArithOp)
arithOp = satisfyToken a
  where
    a TAdd = Just Add
    a TSub = Just Sub
    a TMul = Just Mul
    a TDiv = Just Div
    a _ = Nothing

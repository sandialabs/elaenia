module Frontend.FPCore (
  ParseError (..),
  parsePre,
  parsePreDirective,
) where

import Data.Bifunctor (first)
import Frontend.FPCore.AST (Pred)
import Frontend.FPCore.Lexer (lexer)
import Frontend.FPCore.Parser (Parser, parsePredicate, preDirective)
import Text.Parsec (SourceName, SourcePos, parse)

newtype ParseError = ParseError String
  deriving (Eq, Show)

parsePre :: SourceName -> String -> Either ParseError (Pred SourcePos)
parsePre = runParser parsePredicate

parsePreDirective :: SourceName -> String -> Either ParseError (Pred SourcePos)
parsePreDirective = runParser preDirective

runParser :: Parser a -> SourceName -> String -> Either ParseError a
runParser p path input =
  first (ParseError . show) $
    parse lexer path input >>= parse p path

module Frontend.FPCore.Lexer (
  Lexer,
  Token (..),
  TokenKind (..),
  lexer,
)
where

import Control.Applicative (Alternative ((<|>)))
import Control.Monad (guard)
import Data.Char (digitToInt, isAlpha, isAlphaNum, isAscii, isPrint)
import Data.Functor (($>))
import Data.Ratio ((%))
import Lib (Ident)
import Text.Parsec (Parsec, SourcePos, between, char, choice, digit, eof, getPosition, hexDigit, many, many1, noneOf, notFollowedBy, oneOf, option, satisfy, skipMany, space, try)
import qualified Text.Parsec as Parsec

type Lexer = Parsec String ()

data Token a = Token
  { tokenSourcePos :: a
  , tokenKind :: TokenKind
  }
  deriving (Eq, Show)

data TokenKind
  = TLeftParen
  | TRightParen
  | TLeftBracket
  | TRightBracket
  | TAdd
  | TSub
  | TMul
  | TDiv
  | TGt
  | TLt
  | TGe
  | TLe
  | TEq
  | TNeq
  | TNot
  | TAnd
  | TOr
  | TBang
  | TNumber Rational
  | TString String
  | TPropertyLabel Ident
  | TSymbol Ident
  deriving (Eq, Show)

-- | Tokenize FPCore source.
lexer :: Lexer [Token SourcePos]
lexer = trivia *> many token' <* eof

-- "Trivia is extra bits of source text that don't contribute to the final
-- program. This might include, for example, whitespace and code comments."
--
-- https://www.sv-lang.com/parsing.html
trivia :: Lexer ()
trivia = skipMany (many1 space <|> comment)
  where
    comment :: Lexer String
    comment = char ';' *> many (noneOf ['\r', '\n'])

token' :: Lexer (Token SourcePos)
token' = (Token <$> getPosition <*> tokenKind') <* trivia

tokenKind' :: Lexer TokenKind
tokenKind' =
  choice
    [ TLeftParen <$ leftParen
    , TRightParen <$ rightParen
    , TLeftBracket <$ leftBracket
    , TRightBracket <$ rightBracket
    , TString <$> string
    , TNumber <$> try number {- Number needs to win over symbol whenever the
                                string starts with `+`, `-`, or `.`, but the
                                `try` is also required, since with input
                                like `-x`, `decnum` consumes the `-` before
                                failing. We need to backtrack so that
                                `symbol` can also try to parse the input. -}
    , classifySymbol <$> symbol
    ]

leftParen :: Lexer Char
leftParen = char '('

rightParen :: Lexer Char
rightParen = char ')'

leftBracket :: Lexer Char
leftBracket = char '['

rightBracket :: Lexer Char
rightBracket = char ']'

-- Symbol
--
-- "Any sequence of letters, digits, or characters from the set
-- ~!@$%^&*_-+=<>.?/: not starting with a digit and not matching any other basic
-- token."
--
-- https://fptalks.org/spec/fpcore-2.0.html
--
-- symbol
-- [a-zA-Z~!@$%^&*_\-+=<>.?/:][a-zA-Z0-9~!@$%^&*_\-+=<>.?/:]*
symbol :: Lexer Ident
symbol =
  (:)
    <$> satisfy symbolStart
    <*> many (satisfy symbolCharacter)

symbolStart :: Char -> Bool
symbolStart c = isAlpha c || c `elem` symbolExtraCharacters

symbolCharacter :: Char -> Bool
symbolCharacter c = isAlphaNum c || c `elem` symbolExtraCharacters

symbolExtraCharacters :: String
symbolExtraCharacters = "~!@$%^&*_-+=<>.?/:"

classifySymbol :: Ident -> TokenKind
classifySymbol "+" = TAdd
classifySymbol "-" = TSub
classifySymbol "*" = TMul
classifySymbol "/" = TDiv
classifySymbol ">" = TGt
classifySymbol "<" = TLt
classifySymbol "<=" = TLe
classifySymbol ">=" = TGe
classifySymbol "==" = TEq
classifySymbol "!=" = TNeq
classifySymbol "not" = TNot
classifySymbol "and" = TAnd
classifySymbol "or" = TOr
classifySymbol "!" = TBang
classifySymbol s
  | head s == ':' = TPropertyLabel $ tail s
  | otherwise = TSymbol s

-- String
--
-- "Any sequence of printable characters, spaces, tabs, or carriage returns,
-- delimited by double quotes ("). Within the double quotes, backslashes (\)
-- have special meaning. A backslash followed by a double quote represents a
-- double quote and does not terminate the string; a backslash followed by a
-- backslash represents a backslash; other escapes may also be supported by
-- implementations, but their meaning is not defined in this standard. We
-- recommend that implementations only use escapes defined in the C or Matlab
-- standard libraries."
--
-- https://fptalks.org/spec/fpcore-2.0.html
--
-- string
-- "([\x20-\x21\x23-\x5b\x5d-\x7e]|\\["\\])*"
string :: Lexer String
string = between (char '"') (char '"') (many stringCharacter)

stringCharacter :: Lexer Char
stringCharacter = escapedStringCharacter <|> satisfy unescapedStringCharacter

escapedStringCharacter :: Lexer Char
escapedStringCharacter = char '\\' *> oneOf ['\"', '\\']

unescapedStringCharacter :: Char -> Bool
unescapedStringCharacter c =
  (isAscii c && isPrint c && c /= '"' && c /= '\\')
    || c == '\t'
    || c == '\r'
    || c == '\n'

-- Number
--
-- number ::=
--  | <rational>
--  | <decnum>
--  | <hexnum>
--  | ( digits <decnum> <decnum> <decnum> )
--
-- https://fptalks.org/spec/fpcore-2.0.html
number :: Lexer Rational
number =
  choice
    [ try rational
    , try hexnum
    , decnum
    ]
    <* notFollowedBy (satisfy symbolCharacter)

-- rational
-- [+-]?[0-9]+/[0-9]*[1-9][0-9]*
--
-- https://fptalks.org/spec/fpcore-2.0.html
rational :: Lexer Rational
rational = do
  n <- decimalInteger
  _ <- char '/'
  d <- decimalNatural
  guard (d /= 0)
  pure (n % d)

sign :: (Num a) => Lexer (a -> a)
sign =
  char '-' $> negate
    <|> char '+' $> id
    <|> pure id

decimalNatural :: Lexer Integer
decimalNatural = digitsToInteger 10 <$> many1 digit

decimalInteger :: Lexer Integer
decimalInteger = sign <*> decimalNatural

-- decnum
-- [-+]?([0-9]+(\.[0-9]+)?|\.[0-9]+)(e[-+]?[0-9]+)?
--
-- https://fptalks.org/spec/fpcore-2.0.html
decnum :: Lexer Rational
decnum = do
  s <- sign
  m <- significand' 10 digit
  e <- option 0 (char 'e' *> decimalInteger)
  pure $ s $ m * 10 ^^ e

-- hexnum
-- [+-]?0x([0-9a-f]+(\.[0-9a-f]+)?|\.[0-9a-f]+)(p[-+]?[0-9]+)?
--
-- https://fptalks.org/spec/fpcore-2.0.html
--
-- Note: `hexDigit` also accepts upper case digits which is more lenient than
-- the regex above.
hexnum :: Lexer Rational
hexnum = do
  s <- sign
  _ <- Parsec.string "0x"
  m <- significand' 16 hexDigit
  -- See
  -- https://www.drilian.com/posts/2024.12.30-c-17-style-hex-floats-and-how-to-parse-them/
  e <- option 0 (char 'p' *> decimalInteger)
  pure $ s $ m * 2 ^^ e

-- A significand helper shared by decnum and hexnum. The pattern is either
-- digits with an optional fractional part, or a lone fractional part.
--
-- [0-9]+(\.[0-9]+)?|\.[0-9]+
--
-- Note: name is primed because 'significand` is in the prelude.
significand' :: Integer -> Lexer Char -> Lexer Rational
significand' radix radixDigit = withWhole <|> fractional
  where
    -- [0-9]+(\.[0-9]+)?
    withWhole :: Lexer Rational
    withWhole =
      (+) . fromInteger . digitsToInteger radix
        <$> many1 radixDigit
        <*> option 0 fractional

    -- \.[0-9]+
    fractional :: Lexer Rational
    fractional = fractionValue <$> (char '.' *> many1 radixDigit)
      where
        fractionValue ds = digitsToInteger radix ds % radix ^ length ds

digitsToInteger :: Integer -> String -> Integer
digitsToInteger radix =
  foldl (\n d -> n * radix + toInteger (digitToInt d)) 0

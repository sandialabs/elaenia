module Main (main) where

import Data.Functor (void)
import Data.Ratio ((%))
import Frontend.FPCore (parsePre)
import Frontend.FPCore.ToACSL (acslReal, acslRequires)
import Frontend.FPCore.AST (ArithOp (..), CmpOp (..), Pred (..), Term (..))
import Frontend.FPCore.CComments (spliceAcsl)
import Frontend.FPCore.Lexer (Token (..), TokenKind (..), lexer)
import Test.Hspec (Expectation, Spec, describe, expectationFailure, hspec, it, shouldBe)
import Text.Parsec (parse)

main :: IO ()
main = hspec $ do
  parenSpec
  operatorSpec
  symbolSpec
  numberSpec
  stringSpec
  triviaSpec
  streamSpec
  predSpec
  acslSpec
  ccommentsSpec

-- Helpers

lexesTo :: String -> [TokenKind] -> Expectation
lexesTo input expected =
  fmap (map tokenKind) (parse lexer "" input) `shouldBe` Right expected

rejects :: String -> Expectation
rejects input =
  either
    (const $ pure ())
    (expectationFailure . ("expected a lexer error, got: " ++) . show . map tokenKind)
    (parse lexer "" input)

parenSpec :: Spec
parenSpec = describe "parentheses" $ do
  it "parentheses" $ "()" `lexesTo` [TLeftParen, TRightParen]
  it "square brackets" $ "[]" `lexesTo` [TLeftBracket, TRightBracket]

parsesTo :: String -> Pred () -> Expectation
parsesTo input expected =
  fmap void (parsePre "" input) `shouldBe` Right expected

parseRejects :: String -> Expectation
parseRejects input =
  either
    (const $ pure ())
    (expectationFailure . ("expected a parse error, got: " ++) . show . void)
    (parsePre "" input)

spliceRejects :: String -> Expectation
spliceRejects input =
  either
    (const $ pure ())
    (expectationFailure . ("expected a parse error, got: " ++))
    (spliceAcsl "" input)

-- Operators

operatorSpec :: Spec
operatorSpec = describe "operators and relations" $ do
  it "arithmetic operators" $
    "+ - * /" `lexesTo` [TAdd, TSub, TMul, TDiv]
  it "comparison operators" $
    "> < >= <= == !=" `lexesTo` [TGt, TLt, TGe, TLe, TEq, TNeq]
  it "equality is == not =" $ "=" `lexesTo` [TSymbol "="]
  it "boolean operators" $
    "not and or" `lexesTo` [TNot, TAnd, TOr]

-- Symbols and keywords

symbolSpec :: Spec
symbolSpec = describe "symbols" $ do
  it "identifier" $ "x" `lexesTo` [TSymbol "x"]
  it "alphanumeric" $ "a1" `lexesTo` [TSymbol "a1"]
  it "custom operator" $ "fma" `lexesTo` [TSymbol "fma"]
  it "constant" $ "INFINITY" `lexesTo` [TSymbol "INFINITY"]
  it "negate followed by letter is a symbol" $ "-x" `lexesTo` [TSymbol "-x"]
  it "let*" $ "let*" `lexesTo` [TSymbol "let*"]
  it "symbols can not start with a digit" $ rejects "1x"
  it "annotation bang" $ "!" `lexesTo` [TBang]
  it "property names keep the name after the colon" $
    ":pre :name" `lexesTo` [TPropertyLabel "pre", TPropertyLabel "name"]

-- Numbers

numberSpec :: Spec
numberSpec = describe "numbers" $ do
  describe "decimal numbers" $ do
    it "The answer to the Ultimate Question of Life, the Universe, and Everything" $
      "42" `lexesTo` [TNumber 42]
    it "negative integer" $ "-1" `lexesTo` [TNumber (-1)]
    it "explicit positive sign" $ "+1" `lexesTo` [TNumber 1]
    it "fractional part" $ "1.5" `lexesTo` [TNumber (3 % 2)]
    it "negative fraction" $ "-0.6" `lexesTo` [TNumber ((-3) % 5)]
    it "leading dot" $ ".5" `lexesTo` [TNumber (1 % 2)]
    it "exponent" $ "1e3" `lexesTo` [TNumber 1000]
    it "fraction and negative exponent" $ "1.5e-2" `lexesTo` [TNumber (3 % 200)]
    it "tiny exponent is exact" $
      "-1e-320" `lexesTo` [TNumber (-(1 % (10 ^ (320 :: Integer))))]
    it "trailing period is not a valid token" $ rejects "1."
    it "two periods are not a number" $ rejects "1.5.2"
  describe "rational numbers" $ do
    it "simple rational" $ "1/3" `lexesTo` [TNumber (1 % 3)]
    it "negative rational" $ "-7/2" `lexesTo` [TNumber ((-7) % 2)]
    it "explicit positive sign" $ "+1/2" `lexesTo` [TNumber (1 % 2)]
    it "unreduced rational" $ "6/4" `lexesTo` [TNumber (3 % 2)]
    it "denominator can not be zero" $ rejects "1/0"
    it "denominator can not be many zeros" $ rejects "1/00"
  describe "hexadecimal numbers" $ do
    it "integer" $ "0xff" `lexesTo` [TNumber 255]
    it "uppercase digits" $ "0xFF" `lexesTo` [TNumber 255]
    it "hex significand with zero binary exponent" $ "0x1p0" `lexesTo` [TNumber 1]
    it "hex fractional significand with one exponent" $ "0x1.8p1" `lexesTo` [TNumber 3]
    it "negative exponent" $
      "0x1p-30" `lexesTo` [TNumber (1 % (2 ^ (30 :: Integer)))]
    it "negative hexnum" $ "-0x10" `lexesTo` [TNumber (-16)]
    it "just 0x is not a number" $ rejects "0x"
    it "non-hex digits are rejected" $ rejects "0xg"

-- Strings

stringSpec :: Spec
stringSpec = describe "strings" $ do
  it "hello" $ "\"hello\"" `lexesTo` [TString "hello"]
  it "empty string" $ "\"\"" `lexesTo` [TString ""]
  it "escaped double quote" $
    "\"say \\\"hey\\\"\"" `lexesTo` [TString "say \"hey\""]
  it "escaped backslash" $
    "\"back\\\\slash\"" `lexesTo` [TString "back\\slash"]
  it "multi-line strings occur in FPBench files" $
    "\"line one\nline two\"" `lexesTo` [TString "line one\nline two"]
  it "unterminated string" $ rejects "\"oops"

-- Whitespace and comments

triviaSpec :: Spec
triviaSpec = describe "whitespace and comments" $ do
  it "leading and trailing whitespace" $ "  x  " `lexesTo` [TSymbol "x"]
  it "newlines and tabs between tokens" $
    "(a\n\tb)" `lexesTo` [TLeftParen, TSymbol "a", TSymbol "b", TRightParen]
  it "line comment before tokens" $
    ";;; header\nx" `lexesTo` [TSymbol "x"]
  it "line comment inside a list" $
    "(a ; ignore me\n b)" `lexesTo` [TLeftParen, TSymbol "a", TSymbol "b", TRightParen]
  it "comment ending at end of input" $ "x ; trailing" `lexesTo` [TSymbol "x"]
  it "comments do not extend past the newline" $
    "; comment\nx y" `lexesTo` [TSymbol "x", TSymbol "y"]

-- Example token streams

streamSpec :: Spec
streamSpec = describe "representative FPCore token streams" $ do
  it ":pre from issue 5" $
    ":pre (and (<= -100 u 100) (<= 20 v 20000) (<= -30 T 50))"
      `lexesTo` [ TPropertyLabel "pre"
                , TLeftParen
                , TAnd
                , TLeftParen
                , TLe
                , TNumber (-100)
                , TSymbol "u"
                , TNumber 100
                , TRightParen
                , TLeftParen
                , TLe
                , TNumber 20
                , TSymbol "v"
                , TNumber 20000
                , TRightParen
                , TLeftParen
                , TLe
                , TNumber (-30)
                , TSymbol "T"
                , TNumber 50
                , TRightParen
                , TRightParen
                ]
  it "a whole small FPCore benchmark" $
    "(FPCore (x) :name \"sqrt\" :pre (>= x 0) (sqrt x))"
      `lexesTo` [ TLeftParen
                , TSymbol "FPCore"
                , TLeftParen
                , TSymbol "x"
                , TRightParen
                , TPropertyLabel "name"
                , TString "sqrt"
                , TPropertyLabel "pre"
                , TLeftParen
                , TGe
                , TSymbol "x"
                , TNumber 0
                , TRightParen
                , TLeftParen
                , TSymbol "sqrt"
                , TSymbol "x"
                , TRightParen
                , TRightParen
                ]

-- Preconditions

predSpec :: Spec
predSpec = describe "precondition parser" $ do
  describe "comparisons" $ do
    it "binary comparison" $
      "(!= x 0)" `parsesTo` Compare () Neq [Var () "x", Num () 0]
    it "less than" $
      "(< 1.00001 x 2)" `parsesTo` Compare () Lt [Num () (100001 % 100000), Var () "x", Num () 2]
    it "less equal" $
      "(<= 1 c 9)" `parsesTo` Compare () Le [Num () 1, Var () "c", Num () 9]
    it "rational bounds" $
      "(<= 0 x 3/2)" `parsesTo` Compare () Le [Num () 0, Var () "x", Num () (3 % 2)]
    it "scientific" $
      "(< -1e-5 x0 1.00001)"
        `parsesTo` Compare () Lt [Num () ((-1) % 100000), Var () "x0", Num () (100001 % 100000)]
  describe "and, or, not" $ do
    it "and" $
      "(and (<= -100 u 100) (<= 20 v 20000) (<= -30 T 50))"
        `parsesTo` And
          ()
          [ Compare () Le [Num () (-100), Var () "u", Num () 100]
          , Compare () Le [Num () 20, Var () "v", Num () 20000]
          , Compare () Le [Num () (-30), Var () "T", Num () 50]
          ]
    it "or" $
      "(or (< x 0) (> x 1))"
        `parsesTo` Or
          ()
          [ Compare () Lt [Var () "x", Num () 0]
          , Compare () Gt [Var () "x", Num () 1]
          ]
    it "not" $
      "(not (== x 0))" `parsesTo` Not () (Compare () Eq [Var () "x", Num () 0])
  describe "arithmetic" $ do
    it "quadratic discriminant" $
      "(>= (* b b) (* 4 (* a c)))"
        `parsesTo` Compare
          ()
          Ge
          [ Op () Mul [Var () "b", Var () "b"]
          , Op () Mul [Num () 4, Op () Mul [Var () "a", Var () "c"]]
          ]
    it "constants are variables" $
      "(< 0.05 sl* (* 2 PI))"
        `parsesTo` Compare () Lt [Num () (1 % 20), Var () "sl*", Op () Mul [Num () 2, Var () "PI"]]
  describe "rejections" $ do
    it "unbalanced brackets" $ parseRejects "(< 1 x"
    it "mismatched parentheses and brackets" $ parseRejects "(< 0 (+ 2 3])"
    it "an empty list" $ parseRejects "()"
    it "a bare arithmetic form withou a predicate" $ parseRejects "(+ 1 2)"
    it "a predicate may not be a comparison operand" $ parseRejects "(< (and (< a b)) 3)"
    it "trailing input after the predicate is rejected" $ parseRejects "(< 1 x 2) (< 3 y 4)"

acslSpec :: Spec
acslSpec = describe "ACSL output" $ do
  describe "real literals" $ do
    it "integers" $ acslReal (-100) `shouldBe` "-100"
    it "terminating fraction becomes a decimal" $ acslReal (3 % 2) `shouldBe` "1.5"
    it "small decimal" $ acslReal (1 % 20) `shouldBe` "5.0e-2"
    it "many fractional digits stay exact" $ acslReal (100001 % 100000) `shouldBe` "1.00001"
    it "repeating fraction forces floating-point division" $ acslReal (1 % 3) `shouldBe` "0.3333333333333333"
  describe "requires clauses" $ do
    it "a top-level `and` splits into one `requires` per conjunct" $
      acslRequires
        ( And
            ()
            [ Compare () Le [Num () (-100), Var () "u", Num () 100]
            , Compare () Le [Num () 20, Var () "v", Num () 20000]
            , Compare () Le [Num () (-30), Var () "T", Num () 50]
            ]
        )
        `shouldBe`
          [ "-100 <= u <= 100"
          , "20 <= v <= 20000"
          , "-30 <= T <= 50"
          ]
    it "terms in a comparison get parentheses" $
      acslRequires
        ( Compare
            ()
            Ge
            [ Op () Mul [Var () "b", Var () "b"]
            , Op () Mul [Num () 4, Op () Mul [Var () "a", Var () "c"]]
            ]
        )
        `shouldBe` ["(b * b) >= (4 * (a * c))"]
    it "n-ary `==` expands to adjacent pairs" $
      acslRequires (Compare () Eq [Var () "a", Var () "b", Var () "c"])
        `shouldBe` ["a == b && b == c"]
    it "n-ary `!=` expands to all ordered pairs" $
      acslRequires (Compare () Neq [Var () "a", Var () "b", Var () "c"])
        `shouldBe` ["a != b && a != c && b != c"]

ccommentsSpec :: Spec
ccommentsSpec = describe "C :pre comment translation" $ do
  it "replaces a single-line // :pre with an ACSL block" $
    spliceAcsl "" "// :pre (<= 0 x 1)\ndouble f(double x) { return x; }\n"
      `shouldBe` Right "/*@\n  requires 0 <= x <= 1;\n*/\ndouble f(double x) { return x; }\n"
  it "leaves indented :pre comments untouched" $
    spliceAcsl "" "    // :pre (<= 0 x 1)\n    double f() {}\n"
      `shouldBe` Right "    // :pre (<= 0 x 1)\n    double f() {}\n"
  it "leaves ordinary comments untouched" $
    spliceAcsl "" "// just a note\nint x;\n" `shouldBe` Right "// just a note\nint x;\n"
  it "leaves :precision (not :pre) untouched" $
    spliceAcsl "" "// :precision binary64\nint x;\n" `shouldBe` Right "// :precision binary64\nint x;\n"
  it "rejects trailing tokens after a :pre predicate" $
    spliceRejects "// :pre (<= 0 x 1) extra stuff\ndouble f() {}\n"

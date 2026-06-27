module Frontend.FPCore.CComments (spliceAcsl) where

import Control.Monad (mfilter)
import Data.Char (isSpace)
import Data.List.Extra
import Frontend.FPCore (ParseError, parsePreDirective)
import Frontend.FPCore.ToACSL (acslCommentLines)

spliceAcsl :: String -> String -> Either ParseError String
spliceAcsl path = fmap (unlines . concat) . traverse (renderLine path) . lines

renderLine :: String -> String -> Either ParseError [String]
renderLine path line =
  maybe
    (pure [line])
    (fmap acslCommentLines . parsePreDirective path)
    (mfilter startsPreDirective (stripPrefix "//" line))

startsPreDirective :: String -> Bool
startsPreDirective body =
  maybe
    False
    isPropertyBoundary
    (stripPrefix ":pre" (trimStart body))
  where
    isPropertyBoundary [] = True
    isPropertyBoundary (c : _) = isSpace c || c == '(' || c == '['

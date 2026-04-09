{- HLINT ignore "Use $>" -}
module Frontend.ACSL where

import Text.Parsec
import Data.Char (isSpace)
import Control.Monad (void)
import Data.List (isPrefixOf)

import qualified Language.C as C
import qualified Language.C.Data.Name as C
import qualified Language.C.Data.Position as C


type Parser = Parsec String ()

acslComment :: Parser (SourcePos, SourcePos, [String])
acslComment = do
  startPos <- getPosition
  _ <- try (string "/*@")
  _ <- optional (many (oneOf " \t"))
  _ <- optional endOfLine

  ls <- manyTill acslLine (try (string "*/"))
  endPos <- getPosition

  let reqs = [ (drop 9 . dropSemiColon) l | l <- map stripLeft ls, isRequiresLine l ]
  pure (startPos, endPos, reqs)
  where
    acslLine :: Parser String
    acslLine = do
      line <- manyTill anyChar (lookAhead (void endOfLine <|> void (string "*/")))
      _ <- optional endOfLine
      pure line
    isRequiresLine :: String -> Bool
    isRequiresLine s = "requires" `isPrefixOf` s
    dropSemiColon :: String -> String
    dropSemiColon str = let str' = reverse str in
      reverse $ if ";" `isPrefixOf` str' then drop 1 str' else str'
    stripLeft :: String -> String
    stripLeft = dropWhile isSpace

acslComments :: Parser [(SourcePos, SourcePos, [String])]
acslComments =
      (eof *> pure []) <|> do
      _ <- manyTill anyChar (lookAhead (try (string "/*@")) <|> eof *> pure [])
      (eof *> pure []) <|> do
        c  <- acslComment
        cs <- acslComments
        pure (c : cs)

parseAcslComments :: String -> [([C.CExpr], Int)]
parseAcslComments str = do
  case parse acslComments "" str of
    Left err -> error $ show err
    Right acsls -> map parseCommentBlock acsls

parseCommentBlock :: (SourcePos, SourcePos, [String]) -> ([C.CExpr], Int)
parseCommentBlock (st, end, reqs) =
  case mapM (parseCExpr st) reqs of
    Left err -> error $ show err
    Right reqExps -> (reqExps, sourceLine end)


parseCExpr :: SourcePos -> String -> Either C.ParseError C.CExpr
parseCExpr pos str =
  fst <$> 
    C.execParser 
      C.expressionP 
      (C.inputStreamFromString str) 
      (sourcePosToPosition pos) 
      C.builtinTypeNames 
      (C.namesStartingFrom 0)
  where
    sourcePosToPosition :: SourcePos -> C.Position
    sourcePosToPosition sp =
      C.position
        (-1)   -- offset unknown
        (sourceName sp)
        (sourceLine sp)
        (sourceColumn sp)
        Nothing

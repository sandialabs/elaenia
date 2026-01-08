module Main (main) where

import System.Environment
import System.FilePath

import Imp.Parser
import Imp.TypeChecker
import Imp.Interpreter
import Func.Parser
import Func.TypeChecker
import Func.Interpreter
import Translation.Translator

main :: IO ()
main = do
  (first:rest) <- getArgs
  if first == "--translate" 
    then
      case rest of
        [file] -> case takeExtension file of
          ".imp" -> do
            parseRes <- parseImp file
            case parseRes of
              Left err -> error $ show err
              Right ast -> do
                case typeCheckImp ast of
                  Left err -> error err
                  Right _ -> translImp file
          _    -> error "translation must be provided with a .imp file"
        _    -> error "translation accepts single argument"
    else
      case takeExtension first of
        ".func" -> runFunc first
        ".imp" -> runImp first
        _ -> error "Invalid file type"

  

runImp :: FilePath -> IO ()
runImp path = runProgram path parseImp typeCheckImp interpretImp


runFunc :: FilePath -> IO ()
runFunc path = runProgram path parseFunc typeCheckFunc interpretFunc


runProgram :: Show a =>
     t1
     -> (t1 -> IO (Either a t2))
     -> (t2 -> Either String b)
     -> (t2 -> IO String)
     -> IO ()
runProgram path parse typeCheck interp = do
  parseResult <- parse path
  case parseResult of
    Right ast ->
      case typeCheck ast of
        Left tyErr -> putStrLn tyErr
        Right _    -> do
          res <- interp ast
          putStrLn res
    Left parseErr -> putStrLn $ show parseErr
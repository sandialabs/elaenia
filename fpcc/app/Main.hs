{-# LANGUAGE LambdaCase #-}
module Main (main) where

import System.Environment (getArgs)
import System.Exit (die)
import Frontend.CLang (parse)
import qualified Intermediate.ImpToFunc as I2F
import qualified Intermediate.Linter as L
import qualified Backend.PVS as F2P
import qualified Backend.FPCore.Translator as F2FP
import Backend.FPCore.Pretty (prettyFPCoreProg) 
import qualified PPExt as PVS
import System.FilePath (replaceExtension)


compile :: FilePath -> IO ()
compile path = do
  imp <- parse path
  handleLintErrs $ L.lint imp
  func <- I2F.translate imp
  pvs <- F2P.translate func
  -- fpcore <- F2FP.translate func
  writeFile (replaceExtension path "pvs") (F2P.prettyPrint path pvs)
  -- writeFile (replaceExtension path "fpcore") (show $ prettyFPCoreProg fpcore)

handleLintErrs :: [L.LintError] -> IO ()
handleLintErrs = \case
  [] -> return ()
  errs -> die $ unlines $ map show errs
    


main :: IO ()
main = do
  args <- getArgs
  case args of
    [path] -> do
      compile path
    _ ->
      die "FPCC expects a file path"

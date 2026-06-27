{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TupleSections #-}

module Compiler where

import qualified Intermediate.Linter as L
import Frontend.CLang (parse)
import qualified Intermediate.ImpToFunc as I2F
import Backend.Backend (Backend, BackendOptions (..), runBackendM)

import System.Exit (die)
-- import Intermediate.ImpPretty (ppProgram)
import qualified Data.Map as M
import UserOptions

import Text.Printf (printf)

import Backend.PVS.PVSBackend (pvsBackend)
import Backend.FPCore.FPCoreBackend (fpCoreBackend)
import Frontend.FPCore.CComments (spliceAcsl)


backendOptions :: Options -> BackendOptions
backendOptions opts = M.fromList $
  ("path", opts.inputFile) : maybe [] ((:[]) . ("entryPoint",)) opts.entryPoint

pickBackend :: Options -> IO Backend
pickBackend opts =
  case opts.backend of
    Just "fpcore" -> return fpCoreBackend
    Just "pvs"    -> return pvsBackend
    Just b        -> die $ printf "Invalid backend (%s)" b
    Nothing       -> die "No backend specified (use --backend fpcore|pvs)"




compile :: Options -> IO ()
compile opts = do
  imp <- parse opts.inputFile
  bckend <- pickBackend opts
  -- handleImpDump path imp opts
  handleLintErrs $ L.lint imp
  func <- I2F.translate opts imp
  runBackendM
    (backendOptions opts)
    (bckend opts.inputFile)
    func

translatePre :: Options -> IO ()
translatePre opts = do
  input <- readFile opts.inputFile
  case spliceAcsl opts.inputFile input of
    Left err -> die $ show err
    Right output ->
      let writer = maybe putStr writeFile opts.outputFile
       in writer output

-- handleImpDump :: FilePath -> [Imp.Statement NodeInfo] -> BackendOptions -> IO ()
-- handleImpDump path imp opts
--   | M.lookup "backend" opts == Just "imp" = do
--       let path' = replaceExtension path "imp"
--       writeFile path' (ppProgram imp)
--   | otherwise             = return ()




handleLintErrs :: [L.LintError] -> IO ()
handleLintErrs = \case
  [] -> return ()
  errs -> die $ unlines $ map show errs

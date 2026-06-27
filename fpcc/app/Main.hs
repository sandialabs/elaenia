{-# LANGUAGE OverloadedRecordDot #-}
module Main (main) where

import Compiler (compile, translatePre)

import Options.Applicative
import UserOptions



optsParser :: Parser Options
optsParser =
  Options <$>
    strOption
      (long "input"
      <> metavar "FILE"
      <> help "C Input File")   <*>
    optional (strOption
      (long "backend"
      <> metavar "STRING"
      <> help "Output Format: (fpcore | pvs)"))   <*>
    optional (strOption
      (long "entry-point"
      <> metavar "STRING"
      <> help "Function entry point for FPCore")) <*>
    switch
      (long "vector-write-opt"
      <> long "vwo"
      <> help "Vector write coalescing optimization") <*>
    switch
      (long "pre-to-acsl"
      <> help "Translate // :pre comments in a C file into ACSL /*@ requires */ blocks") <*>
    optional (strOption
      (long "output"
      <> metavar "FILE"
      <> help "Output file (defaults to stdout)"))



main :: IO ()
main = do
  opts' <- execParser opts
  if opts'.preToAcsl
    then translatePre opts'
    else compile opts'
  where
    opts = info (optsParser <**> helper)
      ( fullDesc
      <> progDesc "A C transpiler for automated floating-point error analysis"
      <> header "FPCC")

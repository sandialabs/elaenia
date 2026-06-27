module UserOptions (Options (..)) where

data Options = Options {
  inputFile :: FilePath,
  backend :: Maybe String,
  entryPoint :: Maybe String,
  vectorWriteOpt :: Bool,
  preToAcsl :: Bool,
  outputFile :: Maybe FilePath
}

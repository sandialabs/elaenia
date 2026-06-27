module Backend.PVS.PVSBackend where

import Backend.PVS.PVSTranslator (translatePVS, PVSOutput (PVSOutput), Program)
import Control.Monad.IO.Class (liftIO)
import System.FilePath (takeBaseName, replaceExtension)
import qualified PPExt as P
import Text.Printf (printf)
import Control.Monad ((>=>))

import Intermediate.Func (FuncProg)
import Language.C (NodeInfo)
import Backend.Backend (BackendM)

pvsBackend :: FilePath -> FuncProg NodeInfo -> BackendM NodeInfo ()
pvsBackend path = translatePVS >=> pvsPrinter path

prettyPrint :: String -> Program -> String
prettyPrint moduleName prog = header ++ progString ++ footer
  where
    progString = show $ P.prettyDoc prog
    header = printf "%s: THEORY\nBEGIN\nIMPORTING float@aerr754dp\n\n" moduleName
    footer = printf "\n\nEND %s" moduleName

pvsPrinter :: FilePath -> PVSOutput -> BackendM NodeInfo ()
pvsPrinter path (PVSOutput prog inp)= do
  liftIO $ writeFile pvsFileName (prettyPrint (takeBaseName path) prog)
  liftIO $ writeFile inputDotFileName inp
  where
    pvsFileName = replaceExtension path "pvs"
    inputDotFileName = replaceExtension path "input"
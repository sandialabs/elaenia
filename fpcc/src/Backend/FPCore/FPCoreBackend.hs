module Backend.FPCore.FPCoreBackend where

import Backend.FPCore.FPCoreTranslator (translateFPCore)
import Backend.Backend (BackendM)
import Intermediate.Func (FuncProg)
import Language.C (NodeInfo)

import System.FilePath (replaceExtension)
import Backend.FPCore.Pretty (prettyFPCoreProg)  
import Control.Monad.IO.Class (liftIO)

import Control.Monad ((>=>))

fpCoreBackend :: FilePath -> FuncProg NodeInfo -> BackendM NodeInfo ()
fpCoreBackend path =
  translateFPCore >=> 
    liftIO . 
      writeFile (replaceExtension path "fpcore") . show . prettyFPCoreProg

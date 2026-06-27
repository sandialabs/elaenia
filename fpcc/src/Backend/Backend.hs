module Backend.Backend 
  (Backend,
   BackendOptions,
   backendOption,
   BackendM,
   runBackendM,
   M.fromList
  ) where

import Error ( TranslError )

import qualified Data.Map as M
import Control.Monad.Except (ExceptT, runExceptT)
import System.Exit (die)
import Intermediate.Func (FuncProg)
import Language.C (NodeInfo)
import Control.Monad.Reader (ReaderT (runReaderT), asks)


type BackendOptions = M.Map String String

type BackendM p a = ExceptT (TranslError p) (ReaderT BackendOptions IO) a

backendOption :: String -> BackendM p (Maybe String)
backendOption  = asks . M.lookup

type Backend = FilePath ->
               FuncProg NodeInfo -> 
               BackendM NodeInfo ()

runBackendM :: Show p => BackendOptions -> (t -> BackendM p a) -> t -> IO a
runBackendM opts trnsltr prog =
   (runReaderT . runExceptT . trnsltr) prog opts >>=
    either (die . show) return

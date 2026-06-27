{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}

module Error (TranslError (..),
              throwTranslErr,
              throwTranslErrMsg) where

import Lib (PP, pp)
import Control.Monad.Error.Class (MonadError, throwError)              

data TranslError a where
  TranslError :: Show a => String -> a -> TranslError a
  TranslErrorMsg :: String -> TranslError a
  TranslErrorExp :: PP a => String -> a -> TranslError a

throwTranslErr :: (MonadError (TranslError e) m,  Show e) => String -> e -> m a
throwTranslErr msg n = throwError $ TranslError msg n

throwTranslErrMsg :: (MonadError (TranslError e) m) => String -> m a
throwTranslErrMsg = throwError . TranslErrorMsg 

instance (Show p) => Show (TranslError p) where
  show (TranslError desc nInfo) = desc ++ "\n" ++ show nInfo
  show (TranslErrorExp desc funcExp) = desc ++ "\n" ++ pp funcExp
  show (TranslErrorMsg desc) = desc ++ "\n"


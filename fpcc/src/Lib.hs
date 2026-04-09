{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
module Lib (Ident, 
            Atom,
            dropThrd,
            dropFrth,
            fstOfThree,
            TranslError (..),
            throwTranslErr,
            PP,
            pp
           ) where
import Control.Monad.Error.Class (MonadError, throwError)

type Ident = String

type Atom = String

data TranslError a where
  TranslError :: Show a => String -> a -> TranslError a
  TranslErrorExp :: PP a => String -> a -> TranslError a

throwTranslErr :: (MonadError (TranslError a1) m,  Show a1) => String -> a1 -> m a2
throwTranslErr msg n = throwError $ TranslError msg n

class PP a where
  pp :: a -> String  

instance (Show p) => Show (TranslError p) where
  show (TranslError desc nInfo) = desc ++ "\n" ++ show nInfo
  show (TranslErrorExp desc funcExp) = desc ++ "\n" ++ pp funcExp


dropThrd :: (a,b,c) -> (a,b)
dropThrd (a,b,_) = (a,b)

fstOfThree :: (a,b,c) -> a
fstOfThree (a,_,_) = a

dropFrth :: (a,b,c,d) -> (a,b,c)
dropFrth (a,b,c,_) = (a,b,c)
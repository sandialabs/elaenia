module Lib (Ident, 
            Atom,
            dropThrd,
            dropFrth,
            fstOfThree,
            PP (..),
           ) where

type Ident = String

type Atom = String

class PP a where
  pp :: a -> String  


dropThrd :: (a,b,c) -> (a,b)
dropThrd (a,b,_) = (a,b)

fstOfThree :: (a,b,c) -> a
fstOfThree (a,_,_) = a

dropFrth :: (a,b,c,d) -> (a,b,c)
dropFrth (a,b,c,_) = (a,b,c)
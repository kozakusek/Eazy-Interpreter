module TypeChecker (typeCheck) where

import Eazy.ErrM ( Err )

typeCheck :: a -> Err a
typeCheck = Right
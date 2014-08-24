{-# LANGUAGE GADTs #-}

module Context where

import Language
import Data.Maybe
import Data.Void

-------------------
-- Renamings
-------------------

data Renaming a b where
  DropIt :: Renaming (Maybe a) a
  KeepIt :: Renaming a b -> Renaming (Maybe a) (Maybe b)

rename :: Renaming a b -> a -> b
-- there is no Nothing case: we have substituted that variable!
rename DropIt       = fromJust
rename (KeepIt ren) = fmap $ rename ren

-------------------
-- Contexts
-------------------

newtype Context a = Context { givesTypeTo :: a -> Ty Nf a }

empty :: Context Void
empty = Context absurd

-- Context extensions
-- The dotting pattern corresponds to the elements which
-- are weakened by the constructor.

(.~) :: Context a -> Ty Nf (Maybe a) -> Context (Maybe a)
gamma .~ ty = Context $ \ v ->
                case v of
                  Nothing -> ty
                  Just w  -> wkTy $ gamma `givesTypeTo` w

(.~.) :: Context a -> Ty Nf a -> Context (Maybe a)
gamma .~. ty = gamma .~ wkTy ty

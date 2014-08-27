{-# LANGUAGE GADTs #-}

module Context where

import Language
import Data.Maybe
import Data.Bifunctor
import Data.Void

-------------------
-- Renamings
-------------------

data Renaming a b c d where
  DropItDa :: Renaming (Maybe a) b a b
  DropItTm :: Renaming a (Maybe b) a b
  KeepItDa :: Renaming a b c d -> Renaming (Maybe a) b (Maybe c) d
  KeepItTm :: Renaming a b c d -> Renaming a (Maybe b) c (Maybe d)

rename :: Renaming a b c d -> (a -> c, b -> d)
-- there is no Nothing case: we have substituted that variable!
rename DropItDa       = (fromJust, id)
rename DropItTm       = (id, fromJust)
rename (KeepItDa ren) = bimap fmap id $ rename ren
rename (KeepItTm ren) = bimap id fmap $ rename ren

renameDa = fst . rename
renameTm = snd . rename

-------------------
-- Substitution
-------------------

data Subst a b c d where
  SubstDa :: a -> Ty Nf c d -> Subst a b c d
  SubstTm :: b -> Nf c d    -> Subst a b c d

wkSubstDa :: Subst a b c d -> Subst (Maybe a) b (Maybe c) d
wkSubstDa (SubstDa v u) = SubstDa (Just v) (wkTyDa u)
wkSubstDa (SubstTm v u) = SubstTm v (wkNfDa u)

wkSubstTm :: Subst a b c d -> Subst a (Maybe b) c (Maybe d)
wkSubstTm (SubstDa v u) = SubstDa v (wkTy u)
wkSubstTm (SubstTm v u) = SubstTm (Just v) (wkNf u)

-------------------
-- Contexts
-------------------

newtype Context a b = Context { givesTypeTo :: b -> Ty Nf a b }

empty :: Context Void Void
empty = Context absurd

-- Context extensions
-- The dotting pattern corresponds to the elements which
-- are weakened by the constructor.

(.~) :: Context a b -> Ty Nf a (Maybe b) -> Context a (Maybe b)
gamma .~ ty = Context $ \ v ->
                case v of
                  Nothing -> ty
                  Just w  -> wkTy $ gamma `givesTypeTo` w

(.~.) :: Context a b -> Ty Nf a b -> Context a (Maybe b)
gamma .~. ty = gamma .~ wkTy ty

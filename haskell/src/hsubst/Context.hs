module Context where

import Language
import Data.Maybe
import Data.Void

-------------------
-- Renamings
-------------------

newtype Renaming a b = Renaming { givesNameTo :: a -> b }

wkRen :: Renaming a b -> Renaming (Maybe a) (Maybe b)
wkRen ren = Renaming $ fmap (givesNameTo ren)

dropFst :: Renaming (Maybe a) a
dropFst = Renaming $ fromJust

-------------------
-- Contexts
-------------------

newtype Context a = Context { givesTypeTo :: a -> Nf a }

empty :: Context Void
empty = Context absurd

-- Context extensions

(.~) :: Context a -> Nf (Maybe a) -> Context (Maybe a)
gamma .~ nf = Context $ \ v ->
                case v of
                  Nothing -> nf
                  Just v  -> wkNf $ gamma `givesTypeTo` v

(.~.) :: Context a -> Nf a -> Context (Maybe a)
gamma .~. nf = gamma .~ wkNf nf

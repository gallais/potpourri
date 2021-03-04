module Freer.Section6

import Control.Monad.Error.Interface
import Data.DPair
import Data.List.AtIndex
import Data.OpenUnion
import Freer.Section3p1
import Relation.Binary.Closure.Transitive

%default total

public export
interpose : Member t ts =>
            (a -> Eff ts w) -> (forall v. t v -> Arr ts v w -> Eff ts w) ->
            Eff ts a -> Eff ts w
interpose ret h m = loop m
 where
   loop : Eff ts a -> Eff ts w
   loop (Pure a)  = ret a
   loop t@(Impure u k)  = case prj u of
     Just x => h x (\ v => loop (assert_smaller t (qApp k v)))
     _      => Impure  u (^ \ v => loop (assert_smaller t (qApp k v)))

public export
interface Last (0 t : a) (0 ts : List a) where
  0 atIndex : AtIndex t ts (minus (length ts) 1)

public export
[LAST] {ts : _} -> Last t ts => Member t ts where
  isMember' = Element _ atIndex

public export
Last t (v :: w :: ws) => Last t (u :: v :: w :: ws) where
  atIndex = S atIndex

public export
Last t [v] => Last t [u,v] where
  atIndex = S atIndex

public export
Last t [t] where
  atIndex = Z

{- TODO: look into catch interface
catchDyn : (Last IO ts, HasException e) =>
           Eff ts a -> (e -> Eff ts a) -> Eff ts a
catchDyn m eh = interpose pure handle m where

  handle : IO v -> Arr ts v a -> Eff ts a
  handle = ?a
-}

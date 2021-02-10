module Freer.Section3p2

import Data.DPair
import Data.List
import Data.List.HasLength
import Data.List.AtIndex
import Data.OpenUnion
import Relation.Binary.Closure.Transitive
import Freer.Section3p1

%default total

------------------------------------------------------------------------
-- More utilities

public export
send : Member t ts => t v -> Eff ts v
send m = Impure (inj m) (^ pure)

public export
qComp : Arrs ts a b -> (Eff ts b -> Eff ts' c) -> Arr ts' a c
qComp g h = h . qApp g

public export
handleOrRelay : (a -> Eff ts w) ->
                (forall v. t v -> Arr ts v w -> Eff ts w) ->
                Eff (t :: ts) a -> Eff ts w
handleOrRelay ret h (Pure a) = ret a
handleOrRelay ret h t@(Impure x k) =
  case decomp x of
    Right x => h x (\ v => handleOrRelay ret h (assert_smaller t (qApp k v)))
    Left x =>
      Impure x (^ \ v => handleOrRelay ret h (assert_smaller t (qApp k v)))

public export
run : Eff [] a -> a
run (Pure a) = a
run (Impure x k) = absurd x

------------------------------------------------------------------------
-- Examples

public export
data Reader : Rel Type where
  Get : Reader i i

public export
ask : Member (Reader i) ts => Eff ts i
ask = send Get

public export
addGet : Member (Reader Int) ts => Int -> Eff ts Int
addGet x = do i <- ask
              pure (i + x)

public export
addN : Member (Reader Int) ts => Nat -> Eff ts Int
addN n = foldl (>=>) pure (replicate n addGet) 0

public export
runReader : i -> Eff (Reader i :: ts) a -> Eff ts a
runReader v = handleOrRelay pure (\ Get, k => k v)

public export
data Writer : Rel Type where
  Put : o -> Writer o ()

public export
tell : Member (Writer o) ts => o -> Eff ts ()
tell = send . Put

public export
rdwr : (Member (Reader Int) ts, Member (Writer String) ts) => Eff ts Int
rdwr = do
  tell "begin"
  r <- addN 10
  tell "end"
  pure r

public export
runWriter : Eff (Writer o :: ts) a -> Eff ts (a, List o)
runWriter = handleOrRelay (\ a => pure (a, []))
          $ \ (Put o), k => map (map (o::)) (k ())

public export
runState : Eff (Writer s :: Reader s :: ts) a -> s -> Eff ts (a, s)
runState m v = loop v m where

  0 EFFECTS : List (Type -> Type)
  EFFECTS = (\ a => Writer s a) :: (\ a => Reader s a) :: ts

  loop : s -> Eff EFFECTS a -> Eff ts (a, s)
  loop s (Pure x) = pure (x, s)
  loop s t@(Impure x k) = case decomp x of
    Right (Put o) => loop o (assert_smaller t (qApp k ()))
    Left x => case decomp x of
      Right Get => loop s (assert_smaller t (qApp k s))
      Left x => Impure x (^ \ v => loop s (assert_smaller t (qApp k v)))

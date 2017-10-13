{-# LANGUAGE DataKinds
           , PolyKinds
           , TypeFamilies
           , GADTs
           , TypeOperators
           , ScopedTypeVariables
           , PatternSynonyms
           , AllowAmbiguousTypes
#-}

module Proofs where

infix 2 ==
data (==) :: k -> k -> * where
    Refl :: x == x

sym :: a == b -> b == a
sym Refl = Refl 

trans :: a == b -> b == c -> a == c
trans Refl eq = eq

data From (a :: k) (b :: *) = From b
data To   (a :: k) (b :: *) = To b
data By   (a :: *)          = By a

type EQ a b = From a (To b (By (a == b)))
pattern Eq p = From (To (By p))

infixr 1 .>
(.>) :: forall (a :: k) b c. EQ a b -> EQ b c -> EQ a c
Eq Refl .> eq = eq

proof :: EQ a b -> a == b
proof (Eq eq) = eq

trivial :: By (a == a)
trivial = By Refl

qed :: EQ a a
qed = Eq Refl

data Function :: * -> * -> *

type family Apply (f :: Function a b -> *) (t :: a) :: b

cong :: forall (f :: Function k l -> *) a b. a == b -> Apply f a == Apply f b
cong Refl = Refl


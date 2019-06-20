{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE PolyKinds              #-}

module Simplify where

import Data.Kind

type family IsUnit (a :: Type) :: Bool where
  IsUnit () = 'True
  IsUnit a  = 'False

type family If (b :: Bool) (l :: k) (r :: k) :: k where
  If 'True  l r = l
  If 'False l r = r

type family IsProduct (a :: Type) :: Bool where
  IsProduct (a, b) = 'True
  IsProduct a      = 'False

type family AlgSimpler (a :: Type) (b :: Type) :: Type where
  AlgSimpler a b = If (IsUnit a) b (If (IsUnit b) a (a, b))

type family Simpler' (a :: Type) :: Type where
  Simpler' (a, b) = AlgSimpler (Simpler a) (Simpler b)

type family Simpler (a :: Type) :: Type where
  Simpler a = If (IsProduct a) (Simpler' a) a

class AlgSimplify a b (c :: Bool) (d :: Bool) where
  fromAlgSimpler' :: (IsUnit a ~ c, IsUnit b ~ d) => AlgSimpler a b -> (a, b)
  toAlgSimpler'   :: (IsUnit a ~ c, IsUnit b ~ d) => (a, b) -> AlgSimpler a b

instance AlgSimplify () b 'True d where
  fromAlgSimpler' v = ((), v)
  toAlgSimpler' = snd

instance AlgSimplify a () 'False 'True where
  fromAlgSimpler' v = (v, ())
  toAlgSimpler' = fst

instance AlgSimplify a b 'False 'False where
  fromAlgSimpler' = id
  toAlgSimpler' = id

fromAlgSimpler :: AlgSimplify a b (IsUnit a) (IsUnit b) => AlgSimpler a b -> (a, b)
fromAlgSimpler = fromAlgSimpler'

toAlgSimpler :: AlgSimplify a b (IsUnit a) (IsUnit b) => (a, b) -> AlgSimpler a b
toAlgSimpler = toAlgSimpler'

class Simplify a (b :: Bool) where
  fromSimpler' :: IsProduct a ~ b => Simpler a -> a
  toSimpler'   :: IsProduct a ~ b => a -> Simpler a

instance (Simplify a (IsProduct a), Simplify b (IsProduct b)
         , Simpler a ~ sa, Simpler b ~ sb
         , AlgSimplify sa sb (IsUnit sa) (IsUnit sb))
         => Simplify (a, b) 'True where
  fromSimpler' v =
     let (a, b) = fromAlgSimpler v
     in (fromSimpler a, fromSimpler b)
  toSimpler' (a, b) = toAlgSimpler (toSimpler a, toSimpler b)

instance Simplify a 'False where
  fromSimpler' = id
  toSimpler' = id

fromSimpler :: Simplify a (IsProduct a) => Simpler a -> a
fromSimpler = fromSimpler'

toSimpler :: Simplify a (IsProduct a) => a -> Simpler a
toSimpler = toSimpler'

example :: (Int, (Bool, Integer)) -> (((), ()), (((Int, ()), (Bool, ((), Integer))), ((), ())))
example = fromSimpler

{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE OverloadedStrings      #-}

module Default where

import GHC.TypeLits
import Data.Constraint
import Data.Kind
import Data.Text

data WithDefault k (a :: l) where
  Default :: WithDefault k a
  Value   :: k -> WithDefault k a

setDefault :: k -> WithDefault k a -> WithDefault k a
setDefault k v = case v of
  Default -> Value k
  _ -> v

collapseDefault :: forall k l (a :: l). Known k a => WithDefault k a -> k
collapseDefault x = case x of
  Default -> erase (sing :: Sing k a)
  Value v -> v

data family Sing k (a :: l)

class Known k (a :: l) where
  sing  :: Sing k a
  erase :: Sing k a -> k

data instance Sing Bool b where
  STrue  :: Sing Bool 'True
  SFalse :: Sing Bool 'False

instance Known Bool 'True  where sing = STrue; erase _ = True
instance Known Bool 'False where sing = SFalse; erase _ = False

data instance Sing (Maybe a) (m :: Maybe b) where
  SNothing :: Sing (Maybe a) 'Nothing
  SJust    :: Sing a v -> Sing (Maybe a) ('Just v)

instance Known (Maybe a) ('Nothing :: Maybe b) where
  sing = SNothing
  erase _ = Nothing

instance Known a (v :: b) => Known (Maybe a) ('Just v :: Maybe b) where
  sing            = SJust sing
  erase (SJust v) = Just (erase v)

data instance Sing [a] (xs :: [b]) where
  SNil  :: Sing [a] ('[] :: [b])
  SCons :: Sing a (x :: b) -> Sing [a] xs -> Sing [a] (x ': xs)

instance Known [a] ('[] :: [b]) where sing = SNil; erase _ = []
instance (Known a (x :: b), Known [a] xs) => Known [a] (x ': xs) where
  sing               = SCons sing sing
  erase (SCons x xs) = erase x : erase xs

data instance Sing Text (s :: Symbol) where
  SText :: KnownSymbol s => Sing Text s

instance KnownSymbol s => Known Text s where
  sing  = SText
  erase = pack . symbolVal

data instance Sing (a, b) ('(l , r) :: (c, d)) where
  SPair :: Sing a (l :: c) -> Sing b (r :: d) -> Sing (a, b) '(l , r)

instance (Known a (l :: c), Known b (r :: d)) => Known (a, b) '(l , r) where
  sing              = SPair sing sing
  erase (SPair l r) = (erase l, erase r)

bool :: [Bool]
bool = collapseDefault <$>
     [ Value False
     , Value True
     , Default :: WithDefault Bool 'True
     ]

test :: [[(Bool, Text)]]
test = collapseDefault <$>
     [ Default :: WithDefault [(Bool, Text)] '[ '( 'True , "Hello"), '( 'False , "World") ]
     , Value [(True, "")]
     , Value []
     , Default
     ]


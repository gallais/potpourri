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

data WithDefault' k l (a :: l) where
  Default :: WithDefault' k l a
  Value   :: k -> WithDefault' k l a

type WithDefault (k :: Type) (a :: k) = WithDefault' k k a

setDefault :: k -> WithDefault k a -> WithDefault k a
setDefault k v = case v of
  Default -> Value k
  _ -> v

collapseDefault :: forall k l a. Known k l a => WithDefault' k l a -> k
collapseDefault x = case x of
  Default -> erase (sing :: Sing k l a)
  Value v -> v

data family Sing k l (a :: l)

class Known k l (a :: l) | a -> l where
  sing  :: Sing k l a
  erase :: Sing k l a -> k

data instance Sing Bool Bool b where
  STrue  :: Sing Bool Bool 'True
  SFalse :: Sing Bool Bool 'False

instance Known Bool Bool 'True  where sing = STrue; erase _ = True
instance Known Bool Bool 'False where sing = SFalse; erase _ = False

data instance Sing (Maybe a) (Maybe b) m where
  SNothing :: Sing (Maybe a) (Maybe b) 'Nothing
  SJust    :: Sing a b v -> Sing (Maybe a) (Maybe b) ('Just v)

instance Known (Maybe a) (Maybe b) 'Nothing where
  sing = SNothing
  erase _ = Nothing

instance Known a b v => Known (Maybe a) (Maybe b) ('Just v) where
  sing            = SJust sing
  erase (SJust v) = Just (erase v)

data instance Sing [a] [b] xs where
  SNil  :: Sing [a] [b] '[]
  SCons :: Sing a b x -> Sing [a] [b] xs -> Sing [a] [b] (x ': xs)

instance Known [a] [b] '[] where sing = SNil; erase _ = []
instance (Known a b x, Known [a] [b] xs) => Known [a] [b] (x ': xs) where
  sing    = SCons sing sing
  erase _ = erase (sing :: Sing a b x) : erase (sing :: Sing [a] [b] xs)

data instance Sing Text Symbol s where
  SText :: KnownSymbol s => Sing Text Symbol s

instance KnownSymbol s => Known Text Symbol s where
  sing  = SText
  erase = pack . symbolVal

data instance Sing (a, b) (c, d) '(l , r) where
  SPair :: Sing a c l -> Sing b d r -> Sing (a, b) (c, d) '(l , r)

instance (Known a c l, Known b d r) => Known (a, b) (c, d) '(l , r) where
  sing              = SPair sing sing
  erase (SPair l r) = (erase l, erase r)

test :: [[(Bool, Text)]]
test = collapseDefault <$>
     [ Default :: WithDefault' [(Bool, Text)] [(Bool, Symbol)] '[ '( 'True , "Hello"), '( 'False , "World") ]
     , Value [(True, "")]
     , Value []
     , Default
     ]



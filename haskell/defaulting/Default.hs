{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGe PartialTypeSignatures  #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeOperators          #-}

module Default where

data WithDefault k (a :: k) where
  Default :: WithDefault k a
  Value   :: k -> WithDefault k a

setDefault :: k -> WithDefault k a -> WithDefault k a
setDefault k v = case v of
  Default -> Value k
  _ -> v

collapseDefault :: forall k a. Known k a => WithDefault k a -> k
collapseDefault x = case x of
  Default -> erase (sing :: Sing k a)
  Value v -> v

data family Sing k (a :: k)

class Known k (a :: k) | a -> k where
  sing  :: Sing k a
  erase :: Sing k a -> k

data instance Sing Bool b where
  STrue  :: Sing Bool 'True
  SFalse :: Sing Bool 'False

instance Known Bool 'True  where sing = STrue; erase _ = True
instance Known Bool 'False where sing = SFalse; erase _ = False

data instance Sing [a] xs where
  SNil  :: Sing [a] '[]
  SCons :: Sing a x -> Sing [a] xs -> Sing [a] (x ': xs)

instance Known [a] '[] where sing = SNil; erase _ = []
instance (Known a x, Known [a] xs) => Known [a] (x ': xs) where
  sing    = SCons sing sing
  erase _ = erase (sing :: Sing a x) : erase (sing :: Sing [a] xs)

test :: [[Bool]]
test = collapseDefault <$>
     [ Default :: WithDefault [Bool] '[ 'True, 'False, 'True ]
     , Value [True]
     , Value []
     , Default
     ]



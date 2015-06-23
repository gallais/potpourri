{-# LANGUAGE GADTs          #-}
{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies   #-}

module Context where

import Data.Void

class IsContext a where
  context :: Context a

instance IsContext Void where
  context = SVoid

instance IsContext a => IsContext (Maybe a) where
  context = SMaybe context

data Context a where
  SVoid  :: Context Void
  SMaybe :: Context a -> Context (Maybe a)

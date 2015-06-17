{-# LANGUAGE GADTs          #-}
{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies   #-}

module Context where

import Data.Void

class CContext a where
  context :: Context a

instance CContext Void where
  context = SVoid

instance CContext a => CContext (Maybe a) where
  context = SMaybe context

data Context a where
  SVoid  :: Context Void
  SMaybe :: Context a -> Context (Maybe a)

{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeFamilies #-}

import Data.Kind

data IMaybe (b :: Bool) (a :: Type) where
  IJust :: a -> IMaybe True a
  INothing :: IMaybe False a

type family (||) (b :: Bool) (c :: Bool) :: Bool where
  True || c = True
  False || c = c

data A = A
data B = B
data C = C

data MyType = forall a b c. (a || b || c) ~ True => MyType
  { myTypeA :: IMaybe a A
  , myTypeB :: IMaybe b B
  , myTypeC :: IMaybe c C
  }

myValC :: MyType
myValC = MyType INothing INothing (IJust C)

myValAC :: MyType
myValAC = MyType (IJust A) INothing (IJust C)

fail :: MyType
fail = MyType INothing INothing INothing

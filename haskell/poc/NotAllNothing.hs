{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

import Data.Kind
import Data.Maybe

data IMaybe (b :: Bool) (a :: Type) where
  IJust :: a -> IMaybe True a
  INothing :: IMaybe False a

type family (|||) (b :: Bool) (c :: Bool) :: Bool where
  False ||| c = c
  True ||| c = True

data A = A
data B = B
data C = C

data SBool (b :: Bool) where
  STrue :: SBool True
  SFalse :: SBool False

data MyType
  = forall a b c. (a ||| b ||| c) ~ True => MyType
  { myTypeA :: IMaybe a A
  , myTypeB :: IMaybe b B
  , myTypeC :: IMaybe c C
  }

(|||) :: SBool b -> SBool c -> SBool (b ||| c)
STrue ||| c = STrue
SFalse ||| c = c

data AMaybe ty where
  AMaybe :: SBool b -> IMaybe b ty -> AMaybe ty

aMaybe :: Maybe ty -> AMaybe ty
aMaybe Nothing = AMaybe SFalse INothing
aMaybe (Just v) = AMaybe STrue (IJust v)

data RawMyType = RawMyType (Maybe A) (Maybe B) (Maybe C)

fromRaw :: RawMyType -> Maybe MyType
fromRaw (RawMyType ma mb mc) =
  case aMaybe ma of { AMaybe so1 ma' ->
  case aMaybe mb of { AMaybe so2 mb' ->
  case aMaybe mc of { AMaybe so3 mc' ->
  validate (so1 ||| so2 ||| so3) ma' mb' mc' }}}

validate :: SBool (a ||| b ||| c) ->
            IMaybe a A -> IMaybe b B -> IMaybe c C ->
            Maybe MyType
validate so ma mb mc = case so of
  STrue -> pure (MyType ma mb mc)
  SFalse -> Nothing

myValC :: MyType
myValC = MyType INothing INothing (IJust C)

myValAC :: MyType
myValAC = MyType (IJust A) INothing (IJust C)

aNothing :: Bool
aNothing = isNothing $ fromRaw (RawMyType Nothing Nothing Nothing)

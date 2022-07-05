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

type family Or (bs :: [Bool]) :: Bool where
  Or '[] = False
  Or (True : bs) = True
  Or (False : bs) = Or bs

data A = A
data B = B
data C = C

data SBool (b :: Bool) where
  STrue :: SBool True
  SFalse :: SBool False

data MyType
  = forall a b c. Or [a, b, c] ~ True => MyType
  { myTypeA :: IMaybe a A
  , myTypeB :: IMaybe b B
  , myTypeC :: IMaybe c C
  }

data SList2 (bs :: [Bool]) where
  SNil :: SList2 '[]
  SCons :: SBool b -> SList2 bs -> SList2 (b : bs)

sList2 :: SList2 bs -> SBool (Or bs)
sList2 SNil = SFalse
sList2 (SCons sb sbs) = case sb of
  STrue -> STrue
  SFalse -> sList2 sbs

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
  let sbs = SCons so1 (SCons so2 (SCons so3 SNil)) in
  validate (sList2 sbs) ma' mb' mc' }}}

validate :: SBool (Or [a, b, c]) ->
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

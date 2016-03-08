{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE IncoherentInstances    #-}

module Bidirectional where

import Prelude hiding (lookup)
import Control.Monad.Trans.State
import Data.Proxy
import Data.Monoid

-- Defining type and the corresponding singletons

data Type = TyNat | TyBool | TyFun Type Type
data SType (a :: Type) :: * where
  STyNat  :: SType TyNat
  STyBool :: SType TyBool
  STyFun  :: SType a -> SType b -> SType (TyFun a b)

class CType a where
  sType :: SType a

instance CType TyNat  where sType = STyNat
instance CType TyBool where sType = STyBool
instance (CType a, CType b) => CType (TyFun a b) where
  sType = STyFun sType sType

-- Contexts are lists of types

data Context = Null | Cons Context Type
data SContext (g :: Context) where
  SNull :: SContext Null
  SCons :: SContext g -> SType a -> SContext (Cons g a)

class CContext (g :: Context) where
  sContext :: SContext g

instance CContext Null where
  sContext = SNull

instance (CContext g, CType a) => CContext (Cons g a) where
  sContext = SCons sContext sType

-- Variable are fancy de Bruijn indices

data Var (g :: Context) (a :: Type) where
  Here  :: Var (Cons g a) a
  There :: Var g a -> Var (Cons g b) a

absurd :: Var Null a -> b
absurd v = case v of {}

-- Environments are functions associating a well-scoped and
-- well-typed value to all the variables in range:

newtype Environment (e :: Context -> Type -> *) (g :: Context) (h :: Context) =
  Pack { lookup :: forall a. Var g a -> e h a }

empty :: Environment e Null h
empty = Pack absurd

(#) :: forall e g h a. Environment e g h -> e h a -> Environment e (Cons g a) h
rho # val = Pack snoc where

  snoc :: forall b. Var (Cons g a) b -> e h b
  snoc Here      = val
  snoc (There v) = lookup rho v

-- Inclusions are a special type of environments

type Included = Environment Var

trans :: Included g h -> Environment e h i -> Environment e g i
trans ren rho = Pack $ lookup rho . lookup ren

refl :: Included g g
refl = Pack id

extended :: Included g (Cons g a)
extended = Pack There

step :: Included g h -> Included g (Cons h a)
step = flip trans extended

pop :: Included g h -> Included (Cons g a) (Cons h a)
pop rho = step rho # Here

-- Terms can be defined in a well-scoped, well-typed fashion
-- once more inclusion induces a notion of weakening.

data Nf (g :: Context) (a :: Type) where
  NfTrue  :: Nf g TyBool
  NfFalse :: Nf g TyBool
  NfZero  :: Nf g TyNat
  NfSucc  :: Nf g TyNat -> Nf g TyNat
  NfLam   :: Nf (Cons g a) b -> Nf g (TyFun a b)
  NfEmb   :: Ne g a -> Nf g a

data Ne (g :: Context) (a :: Type) where
  NeVar :: Var g a -> Ne g a
  NeITE :: Ne g TyBool -> Nf g a -> Nf g a -> Ne g a
  NeApp :: SType a -> Ne g (TyFun a b) -> Nf g a -> Ne g b
  NeRec :: SType a -> Nf g a -> Nf g (TyFun TyNat (TyFun a a)) -> Ne g TyNat -> Ne g a
  NeCut :: Nf g a -> Ne g a

newtype EnvString (g :: Context) (a :: Type) = EnvString { runString :: String }

showNf :: Environment EnvString g h -> Nf g a -> State [String] String
showNf rho (NfLam b) = do
  (hd : tl) <- get
  put tl
  (("\\" <> hd <> ".") <>) <$> showNf (rho # EnvString hd) b
showNf rho t = case t of
  NfTrue   -> return "True"
  NfFalse  -> return "False"
  NfZero   -> return "Zero"
  NfSucc n -> ("Succ " <>) <$> showNf rho n
  NfEmb ne -> showNe rho ne

showIfte b l r = "if " <> b <> " then " <> l <> " else " <> r
showApp f t    = f <> " (" <> t <> ")"
showRec z s n  = "rec[ " <> z <> ", " <> s <> ", " <> n <> " ]"

showNe :: Environment EnvString g h -> Ne g a -> State [String] String
showNe rho t = case t of
  NeVar v       -> return $ runString $ lookup rho v
  NeITE b l r   -> showIfte <$> showNe rho b <*> showNf rho l <*> showNf rho r
  NeApp ty f t  -> showApp  <$> showNe rho f <*> showNf rho t
  NeRec p z s n -> showRec  <$> showNf rho z <*> showNf rho s <*> showNe rho n
  NeCut tm      -> showNf rho tm


nameSupply :: [String]
nameSupply = concatMap (\ s -> fmap (:s) alpha) $ [] : num where
  alpha = "abcdefghijklmnopqrstuvwyz"
  num   = fmap show [1..]

initEnv :: forall g h. SContext g -> State [String] (Environment EnvString g h)
initEnv SNull       = return empty
initEnv (SCons g _) = do
  (hd : tl) <- get
  put tl
  rest <- initEnv g
  return $ rest # EnvString hd

instance CContext g => Show (Nf g a) where
  show t = evalState (initEnv sContext >>= flip showNf t) nameSupply where

instance CContext g => Show (Ne g a) where
  show t = evalState (initEnv sContext >>= flip showNe t) nameSupply where


class Extension (g :: Context) (h :: Context) (b :: Bool) where
  steps :: Proxy b -> Included g h


instance Extension g g b where
  steps _ = refl

instance Extension g h (LT g h) => Extension g (Cons h a) True where
  steps _ = step $ steps (Proxy :: Proxy (LT g h))

newtype FreshVar g a =
  FreshVar { varNe :: forall h. Extension (Cons g a) h (LT (Cons g a) h) => Ne h a }

varNf :: forall g h a. Extension (Cons g a) h (LT (Cons g a) h) => FreshVar g a -> Nf h a
varNf = NfEmb . varNe

lam :: forall g a b. (FreshVar g a -> Nf (Cons g a) b) -> Nf g (TyFun a b)
lam b = NfLam $ b $ FreshVar $ NeVar freshVar where

  freshVar :: forall h. Extension (Cons g a) h (LT (Cons g a) h) => Var h a
  freshVar = lookup (steps (Proxy :: Proxy (LT (Cons g a) h))) (Here :: Var (Cons g a) a)


identity :: Nf g (TyFun a a)
identity = lam $ \ x -> varNf x


true :: Nf g (TyFun a (TyFun b a))
true = lam $ \ x ->
       lam $ \ y ->
       varNf x

false :: Nf g (TyFun a (TyFun b b))
false = lam $ \ _ -> identity


type family EQ x y where
  EQ x x = True
  EQ x y = False

type family OR (b :: Bool) (c :: Bool) where
  OR True c  = True
  OR b True  = True
  OR b False = b
  OR False c = c

type family LT (g :: Context) (h :: Context) where
  LT g (Cons h a) = LE g h
  LT g h          = False

type family LE (g :: Context) (h :: Context) where
  LE g h = OR (EQ g h) (LT g h)

-- SYNTAX EXAMPLES

addARGH :: Nf g (TyFun TyNat (TyFun TyNat TyNat))
addARGH =
  NfLam {- m -} $
  NfLam {- n -} $
  NfEmb $ NeRec STyNat
                (NfEmb $ NeVar Here)
                (NfLam $ NfLam $ NfSucc (NfEmb $ NeVar Here))
                (NeVar $ There Here)

mulARGH :: Nf g (TyFun TyNat (TyFun TyNat TyNat))
mulARGH =
  NfLam {- m -} $
  NfLam {- n -} $
  NfEmb $ NeRec STyNat
                NfZero
                (NfLam $ NfLam $
                let m = There $ There Here in
                NfEmb $ NeApp STyNat (NeApp STyNat (NeCut addARGH) (NfEmb $ NeVar m)) (NfEmb $ NeVar Here))
                (NeVar $ There Here)

add :: Nf g (TyFun TyNat (TyFun TyNat TyNat))
add =
  lam $ \ m ->
  lam $ \ n ->
  NfEmb $ NeRec STyNat
                (varNf n)
                (lam $ \ _ -> lam $ \ ih -> NfSucc $ varNf ih)
                (varNe m)

mul :: Nf g (TyFun TyNat (TyFun TyNat TyNat))
mul =
  lam $ \ m ->
  lam $ \ n ->
  NfEmb $ NeRec STyNat
                NfZero
                (lam $ \ _ -> lam $ \ ih ->
                NfEmb $ NeApp STyNat (NeApp STyNat (NeCut add) (varNf n)) (varNf ih))
                (varNe m)


two :: Nf Null TyNat
two = NfSucc $ NfSucc NfZero

three :: Nf Null TyNat
three = NfSucc two

five :: Nf Null TyNat
five = NfEmb $ NeApp STyNat (NeApp STyNat (NeCut add) three) two


main :: IO ()
main = do
  print (identity :: Nf 'Null ('TyFun 'TyNat 'TyNat))
  print (true     :: Nf 'Null ('TyFun 'TyNat ('TyFun 'TyBool 'TyNat)))
  print (false    :: Nf 'Null ('TyFun 'TyNat ('TyFun 'TyBool 'TyBool)))
  mapM_ print [two, three, five]


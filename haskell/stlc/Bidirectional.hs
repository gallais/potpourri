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
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE RecordWildCards        #-}
{-# OPTIONS -Wall                   #-}

module Bidirectional where

import Prelude hiding (lookup)
import Control.Monad.Trans.State
import Data.Proxy
import Data.Monoid

-- Defining type and the corresponding singletons

data Type = TyNat | TyBool | TyFun Type Type
infixr 5 :->
type (:->) = 'TyFun

data SType (a :: Type) :: * where
  STyNat  :: SType 'TyNat
  STyBool :: SType 'TyBool
  STyFun  :: SType a -> SType b -> SType (a :-> b)

instance Show (SType a) where
  show ty = case ty of
    STyNat     -> "ℕ"
    STyBool    -> "𝔹"
    STyFun a b -> show a <> " -> " <> show b

class CType a where
  sType :: SType a

instance CType 'TyNat  where sType = STyNat
instance CType 'TyBool where sType = STyBool
instance (CType a, CType b) => CType (a :-> b) where
  sType = STyFun sType sType

-- Contexts are lists of types

data Context = Null | Cons Context Type
infixl 3 :>
type (:>) = 'Cons
data SContext (g :: Context) where
  SNull :: SContext 'Null
  SCons :: SContext g -> SType a -> SContext (g :> a)

class CContext (g :: Context) where
  sContext :: SContext g

instance CContext 'Null where
  sContext = SNull

instance (CContext g, CType a) => CContext (g :> a) where
  sContext = SCons sContext sType

-- Variable are fancy de Bruijn indices

data Var (g :: Context) (a :: Type) where
  Here  :: Var (g :> a) a
  There :: Var g a -> Var (g :> b) a

absurd :: Var 'Null a -> b
absurd v = case v of {}

-- Environments are functions associating a well-scoped and
-- well-typed value to all the variables in range:

newtype Environment (e :: Context -> Type -> *) (g :: Context) (h :: Context) =
  Pack { lookup :: forall a. Var g a -> e h a }

empty :: Environment e 'Null h
empty = Pack absurd

(#) :: forall e g h a. Environment e g h -> e h a -> Environment e (g :> a) h
rho # val = Pack snoc where

  snoc :: forall b. Var (g :> a) b -> e h b
  snoc Here      = val
  snoc (There v) = lookup rho v

-- Inclusions are a special type of environments

type Included = Environment Var

trans :: Included g h -> Environment e h i -> Environment e g i
trans ren rho = Pack $ lookup rho . lookup ren

wkEnv :: Weakening e -> Included h i -> Environment e g h -> Environment e g i
wkEnv wk inc rho = Pack $ wk inc . lookup rho

refl :: Included g g
refl = Pack id

step :: Included g h -> Included g (h :> a)
step = flip trans extended

extended :: Included g (g :> a)
extended = Pack There

pop :: Included g h -> Included (g :> a) (h :> a)
pop rho = step rho # Here

-- Terms can be defined in a well-scoped, well-typed fashion
-- once more inclusion induces a notion of weakening.

data Nf (g :: Context) (a :: Type) where
  NfTrue  :: Nf g 'TyBool
  NfFalse :: Nf g 'TyBool
  NfZero  :: Nf g 'TyNat
  NfSucc  :: Nf g 'TyNat -> Nf g 'TyNat
  NfLam   :: Nf (g :> a) b -> Nf g (a :-> b)
  NfEmb   :: Ne g a -> Nf g a

data Ne (g :: Context) (a :: Type) where
  NeVar :: Var g a -> Ne g a
  NeITE :: SType a -> Ne g 'TyBool -> Nf g a -> Nf g a -> Ne g a
  NeApp :: Ne g (a :-> b) -> Nf g a -> Ne g b
  NeRec :: SType a -> Nf g a -> Nf g ('TyNat :-> a :-> a) -> Ne g 'TyNat -> Ne g a
  NeCut :: Nf g a -> SType a -> Ne g a

--

type Weakening (t :: Context -> Type -> *) = forall g h a. Included g h -> t g a -> t h a
type Kripke (e :: Context -> Type -> *) (v :: Context -> Type -> *)
            (g :: Context) (a :: Type) (b :: Type) =
  forall h. Included g h -> e h a -> v h b

data Model
  (env :: Context -> Type -> *)
  (vnf :: Context -> Type -> *)
  (vne :: Context -> Type -> *)
  = Model
  { -- ENV
    reflects :: forall g. Environment env g g
  , envWeak  :: Weakening env
    -- VNF
  , vnfTrue  :: forall g. vnf g 'TyBool
  , vnfFalse :: forall g. vnf g 'TyBool
  , vnfZero  :: forall g. vnf g 'TyNat
  , vnfSucc  :: forall g. vnf g 'TyNat -> vnf g 'TyNat
  , vnfLam   :: forall g a b. Kripke env vnf g a b -> vnf g (a :-> b)
  , vnfEmb   :: forall g a. vne g a -> vnf g a
    -- VNE
  , vneVar   :: forall g a. env g a -> vne g a
  , vneITE   :: forall g a. SType a -> vne g 'TyBool -> vnf g a -> vnf g a -> vne g a
  , vneApp   :: forall g a b. vne g (a :-> b) -> vnf g a -> vne g b
  , vneRec   :: forall g a. SType a -> vnf g a -> vnf g ('TyNat :-> a :-> a) -> vne g 'TyNat -> vne g a
  , vneCut   :: forall g a. vnf g a -> SType a -> vne g a
  }

type Evaluation
     (trm :: Context -> Type -> *)
     (env :: Context -> Type -> *)
     (val :: Context -> Type -> *) =
     forall g h a. trm g a -> Environment env g h -> val h a

evalNe :: Model env vnf vne -> Evaluation Ne env vne
evalNe m@Model{..} ne rho = case ne of
  NeVar v        -> vneVar (lookup rho v)
  NeITE ty b l r -> vneITE ty (evalNe m b rho) (evalNf m l rho) (evalNf m r rho)
  NeApp f t      -> vneApp (evalNe m f rho) (evalNf m t rho)
  NeRec p z s n  -> vneRec p (evalNf m z rho) (evalNf m s rho) (evalNe m n rho)
  NeCut f ty     -> vneCut (evalNf m f rho) ty

evalNf :: Model env vnf vne -> Evaluation Nf env vnf
evalNf m@Model{..} t rho = case t of 
  NfTrue   -> vnfTrue
  NfFalse  -> vnfFalse
  NfZero   -> vnfZero
  NfSucc n -> vnfSucc $ evalNf m n rho
  NfLam b  -> vnfLam $ \ inc v -> evalNf m b (wkEnv envWeak inc rho # v)
  NfEmb ne -> vnfEmb $ evalNe m ne rho

--
renaming :: Model Var Nf Ne
renaming = Model
  { reflects = Pack id
  , envWeak  = lookup
  , vnfTrue  = NfTrue
  , vnfFalse = NfFalse
  , vnfZero  = NfZero
  , vnfSucc  = NfSucc
  , vnfLam   = \ b -> NfLam $ b extended Here
  , vnfEmb   = NfEmb
  , vneVar   = NeVar
  , vneApp   = NeApp
  , vneITE   = NeITE
  , vneRec   = NeRec
  , vneCut   = NeCut
  }

substitution :: Model Ne Nf Ne
substitution = Model
  { reflects = Pack NeVar
  , envWeak  = weaken
  , vnfTrue  = NfTrue
  , vnfFalse = NfFalse
  , vnfZero  = NfZero
  , vnfSucc  = NfSucc
  , vnfLam   = \ b -> NfLam $ b extended (NeVar Here)
  , vnfEmb   = NfEmb
  , vneVar   = id
  , vneApp   = NeApp
  , vneITE   = NeITE
  , vneRec   = NeRec
  , vneCut   = NeCut
  }

--
newtype EnvString (g :: Context) (a :: Type) = EnvString { runString :: String }

showNf :: Environment EnvString g h -> Nf g a -> State [String] String
showNf rho t = case t of
  NfLam b  -> do
    (hd : tl) <- get
    put tl
    (("\\" <> hd <> ".") <>) <$> showNf (rho # EnvString hd) b
  NfTrue   -> return "True"
  NfFalse  -> return "False"
  NfZero   -> return "Zero"
  NfSucc n -> ("Succ " <>) <$> showNf rho n
  NfEmb ne -> showNe rho ne

showIfte :: String -> String -> String -> String
showIfte b l r = "if " <> b <> " then " <> l <> " else " <> r
showApp :: String -> String -> String
showApp f t    = f <> " (" <> t <> ")"
showRec :: String -> String -> String -> String -> String
showRec ty z s n  = "rec[ " <> ty <> ", " <> z <> ", " <> s <> ", " <> n <> " ]"
showCut :: String -> String -> String
showCut tm ty  = "(" <> tm <> " :: " <> ty <> ")"

showNe :: Environment EnvString g h -> Ne g a -> State [String] String
showNe rho ne = case ne of
  NeVar v       -> return $ runString $ lookup rho v
  NeITE _ b l r -> showIfte <$> showNe rho b  <*> showNf rho l <*> showNf rho r
  NeApp f t     -> showApp  <$> showNe rho f  <*> showNf rho t
  NeRec p z s n -> showRec  <$> pure (show p) <*> showNf rho z <*> showNf rho s <*> showNe rho n
  NeCut tm ty   -> showCut  <$> showNf rho tm <*> pure (show ty)


nameSupply :: [String]
nameSupply = concatMap (\ s -> fmap (:s) alpha) $ [] : num where
  alpha = "abcdefghijklmnopqrstuvwyz"
  num   = fmap show ([1..] :: [Integer])

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

instance Extension g h (LT g h) => Extension g ('Cons h a) 'True where
  steps _ = step $ steps (Proxy :: Proxy (LT g h))

newtype FreshVar g a =
  FreshVar { runFreshVar :: forall h. Extension (g :> a) h (LT (g :> a) h) => Ne h a }

class FreshVariable (v :: Context -> Type -> *) where
  var :: forall g h a. Extension (g :> a) h (LT (g :> a) h) => FreshVar g a -> v h a

instance FreshVariable Ne where
  var = runFreshVar

instance FreshVariable Nf where
  var = NfEmb . runFreshVar

lam :: forall g a b. (FreshVar g a -> Nf (g :> a) b) -> Nf g (a :-> b)
lam b = NfLam $ b $ FreshVar $ NeVar freshVar where

  freshVar :: forall h. Extension (g :> a) h (LT (g :> a) h) => Var h a
  freshVar = lookup (steps (Proxy :: Proxy (LT (g :> a) h))) (Here :: Var (g :> a) a)


identity :: Nf g (a :-> a)
identity = lam $ \ x -> var x

true :: Nf g (a :-> b :-> a)
true = lam $ \ x ->
       lam $ \ _ ->
       var x

false :: Nf g (a :-> b :-> b)
false = lam $ \ _ -> identity


type family EQ x y where
  EQ x x = 'True
  EQ x y = 'False

type family OR (b :: Bool) (c :: Bool) where
  OR 'True c  = 'True
  OR b 'True  = 'True
  OR b 'False = b
  OR 'False c = c

type family LT (g :: Context) (h :: Context) where
  LT g (h :> a) = LE g h
  LT g h        = 'False

type family LE (g :: Context) (h :: Context) where
  LE g h = OR (EQ g h) (LT g h)

-- SYNTAX EXAMPLES

tyAdd :: SType ('TyNat :-> 'TyNat :-> 'TyNat)
tyAdd = STyFun STyNat (STyFun STyNat STyNat)

addARGH :: Nf g ('TyNat :-> 'TyNat :-> 'TyNat)
addARGH =
  NfLam {- m -} $
  NfLam {- n -} $
  NfEmb $ NeRec STyNat
                (NfEmb $ NeVar Here)
                (NfLam $ NfLam $ NfSucc (NfEmb $ NeVar Here))
                (NeVar $ There Here)

mulARGH :: Nf g ('TyNat :-> 'TyNat :-> 'TyNat)
mulARGH =
  NfLam {- m -} $
  NfLam {- n -} $
  NfEmb $ NeRec STyNat
                NfZero
                (NfLam $ NfLam $
                let m = There $ There Here in
                NfEmb $ NeApp (NeApp (NeCut addARGH tyAdd) (NfEmb $ NeVar m)) (NfEmb $ NeVar Here))
                (NeVar $ There Here)

add :: Nf g ('TyNat :-> 'TyNat :-> 'TyNat)
add =
  lam $ \ m ->
  lam $ \ n ->
  NfEmb $ NeRec STyNat
                (var n)
                (lam $ \ _ -> lam $ \ ih -> NfSucc $ var ih)
                (var m)

mul :: Nf g ('TyNat :-> 'TyNat :-> 'TyNat)
mul =
  lam $ \ m ->
  lam $ \ n ->
  NfEmb $ NeRec STyNat
                NfZero
                (lam $ \ _ -> lam $ \ ih ->
                NfEmb $ NeApp (NeApp (NeCut add tyAdd) (var n)) (var ih))
                (var m)

class Weakenable (t :: Context -> Type -> *) where
  weaken :: Weakening t

  weak :: forall g h a. Extension g h (LT g h) => t g a -> t h a
  weak = weaken $ steps (Proxy :: Proxy (LT g h))

instance Weakenable Var where
  weaken = lookup

instance Weakenable Nf where
  weaken = flip (evalNf renaming)

instance Weakenable Ne where
  weaken = flip (evalNe renaming)

isZero :: Nf g ('TyNat :-> 'TyBool)
isZero =
  lam $ \ m ->
  NfEmb $ NeRec STyBool
                NfTrue
                (lam $ \ _ -> lam $ \ _ -> NfFalse)
                (var m)

two :: Nf 'Null 'TyNat
two = NfSucc $ NfSucc NfZero

three :: Nf 'Null 'TyNat
three = NfSucc two

five :: Nf 'Null 'TyNat
five = NfEmb $ NeApp (NeApp (NeCut add tyAdd) three) two


main :: IO ()
main = do
  print (identity :: Nf 'Null ('TyNat :-> 'TyNat))
  print (true     :: Nf 'Null ('TyNat :-> 'TyBool :-> 'TyNat))
  print (false    :: Nf 'Null ('TyNat :-> 'TyBool :-> 'TyBool))
  print (isZero   :: Nf 'Null ('TyNat :-> 'TyBool))
  mapM_ print [two, three, five]


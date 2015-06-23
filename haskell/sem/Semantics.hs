{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards       #-}

module Semantics where

import GHC.Prim
import Control.Applicative
import Control.Monad
import Control.Monad.State
import Data.Void
import Context
import Term

class UnConstrained a where
instance UnConstrained a where

data Semantics e m (cE :: * -> Constraint) =
  Semantics -- concerning environment values
            { weak  :: forall a b. (a -> b) -> e a -> e b
            , embed :: forall a. cE a => a -> e a
            -- concerning model values
            , var    :: forall a. e a -> m a
            , apply  :: forall a. m a -> m a -> m a
            , lambda :: forall a. (forall b. (a -> b) -> e b -> m b) -> m a
            }

semantics :: Semantics e m cE -> Term a -> (a -> e b) -> m b
semantics sem (Var a)   rho = var sem $ rho a
semantics sem (App f t) rho = apply sem (semantics sem f rho) (semantics sem t rho)
semantics sem (Lam b)   rho = lambda sem $ \ f e -> semantics sem b (maybe e $ weak sem f . rho)

eval :: cE a => Semantics e m cE -> Term a -> m a
eval sem t = semantics sem t $ embed sem

-- showing
newtype Constant b a = Constant { runConstant :: b }
instance Functor (Constant b) where fmap f = Constant . runConstant

showing :: Semantics (Constant String) (Constant (State [String] String)) Show
showing =
  Semantics { weak   = fmap
            , embed  = Constant . show
            , var    = Constant . return . runConstant
            , apply  = \ mf mt -> Constant $ do
                                    f <- runConstant mf
                                    t <- runConstant mt
                                    return $ '(' : f ++ ") " ++ t
            , lambda = \ t -> Constant $ do
                                (x : xs) <- get
                                ()       <- put xs
                                body     <- runConstant $ t Just (Constant x)
                                return $ '\\' : x ++ ". " ++ body
            }

--nameContext :: Context a -> State [String] (a -> Constant String a)
--nameContext SVoid      = return absurd
--nameContext (SMaybe c) = do
--  rest     <- nameContext c
--  (x : xs) <- get
--  ()       <- put xs
--  return $ maybe (Constant x) (fmap Just . rest)

--displayTerm :: Context a -> Term a -> State [String] String
--displayTerm c t = do
--  ctx <- nameContext c
--  runConstant $ semantics showing t ctx

instance Show a => Show (Term a) where
  show t =
    let firstNames = "xyz" ++ ['a'..'w']
        otherNames = [1..] >>= \ i -> fmap (: show i) firstNames
    in evalState (runConstant $ eval showing t) $ fmap (:[]) firstNames ++ otherNames

--instance IsContext a => Show (Term a) where
--  show t =
--    let firstNames = "xyz" ++ ['a'..'w']
--        otherNames = [1..] >>= \ i -> fmap (: show i) firstNames
--    in evalState (displayTerm context t) $ fmap (:[]) firstNames ++ otherNames

instance Show ClosedTerm where
  show = show . term

-- renaming
newtype Identity a = Identity { runIdentity :: a }
instance Functor Identity where fmap f = Identity . f . runIdentity

renaming :: Semantics Identity Term UnConstrained
renaming =
  Semantics { weak   = fmap
            , embed  = Identity
            , var    = Var . runIdentity
            , apply  = App
            , lambda = \ t -> Lam $ t Just (Identity Nothing)
            }

-- parallel substitution
instance Functor Term where fmap f t = semantics renaming t (Identity . f)

substitution :: Semantics Term Term UnConstrained
substitution =
  Semantics { weak   = fmap
            , embed  = Var
            , var    = id
            , apply  = App
            , lambda = \ t -> Lam $ t Just (Var Nothing)
            }

instance Applicative Term where
  pure  = return
  (<*>) = ap

instance Monad Term where
  return = Var
  (>>=)  = semantics substitution

-- evaluation
data Model a =
    Base (Term a)
  | MLam  (forall b. (a -> b) -> Model b -> Model b)

instance Functor Model where
  fmap f (Base t)   = Base $ fmap f t
  fmap f (MLam t)   = MLam $ t . (. f)

reify :: Model a -> Term a
reify (Base t) = t
reify (MLam t) = Lam $ reify $ t Just $ Base $ Var Nothing

beta :: Model a -> Model a -> Model a
beta (MLam t) u = t id u

normalisation :: Semantics Model Model UnConstrained
normalisation =
  Semantics { weak   = fmap
            , embed  = Base . Var
            , var    = id
            , apply  = beta
            , lambda = MLam
            }

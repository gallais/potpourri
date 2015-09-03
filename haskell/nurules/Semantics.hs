{-# OPTIONS  -Wall               #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Semantics where

import Data.Sequence

import Context as Context
import Language
import Control.Monad.State

----------------------------------------------------
-- SEMANTICS
-- A semantics is indexed by the domains in which the various notions
-- are interpreted and packs combinators explaining the meaning of the
-- various term constructors.
----------------------------------------------------

data Semantics
      (e  :: Context -> *) -- Environment
      (i  :: Context -> *) -- Infer
      (bd :: Context -> *) -- Binder
      (c  :: Context -> *) -- Check
      (el :: Context -> *) -- Elim
      (sp :: Context -> *) -- Spine
      = Semantics
  {
  -- ENVIRONMENT
    weak  :: forall g d. Renaming g d -> e g -> e d
  , embed :: forall g. Var g -> e g
  -- INFER
  , var   :: forall g. e g -> i g
  , cut   :: forall g. i g -> sp g -> i g
  , ann   :: forall g. c g -> c g -> i g
  -- BINDER
  , lam   :: forall g. bd g
  , piT   :: forall g. c g -> bd g
  , letx  :: forall g. i g -> bd g
  -- CHECK
  , bnd   :: forall g. bd g -> (forall d. Renaming g d -> e d -> c d) -> c g
  , zro   :: forall g. c g
  , suc   :: forall g. c g -> c g
  , emb   :: forall g. i g -> c g
  , nat   :: forall g. c g
  , set   :: forall g. c g
  -- ELIM
  , app   :: forall g. c g -> el g
  , rec   :: forall g. c g -> c g -> c g -> el g
  -- SPINE
  , spine :: forall g. Seq (el g) -> sp g
  }

----------------------------------------------------
-- FUNDAMENTAL LEMMA OF SEMANTICS
----------------------------------------------------

lemmaCheck :: forall e i bd c el sp. Semantics e i bd c el sp ->
              forall d g. Check g -> Environment d e g -> c d
lemmaCheck sem@Semantics{..} = go where
  go :: forall d' g'. Check g' -> Environment d' e g' -> c d'
  go (Bnd bd c) rho = bnd (lemmaBinder sem bd rho)
                      $ \ ren v -> go c $ (weak ren . rho) `cons` v
  go Zro        _   = zro
  go (Suc n)    rho = suc $ go n rho
  go (Emb i)    rho = emb $ lemmaInfer sem i rho
  go Nat        _   = nat
  go Set        _   = set

lemmaBinder :: forall e i bd c el sp. Semantics e i bd c el sp ->
               forall d g. Binder g -> Environment d e g -> bd d
lemmaBinder sem@Semantics{..} = go where
  go Lam     _   = lam
  go (Pi a)  rho = piT $ lemmaCheck sem a rho
  go (Let i) rho = letx $ lemmaInfer sem i rho

lemmaInfer :: forall e i bd c el sp. Semantics e i bd c el sp ->
               forall d g. Infer g -> Environment d e g -> i d
lemmaInfer sem@Semantics{..} = go where
  go (Var v)     rho = var $ rho v
  go (Cut i els) rho = cut (go i rho) (lemmaSpine sem els rho)
  go (Ann c ty)  rho = ann (lemmaCheck sem c rho) (lemmaCheck sem ty rho)

lemmaSpine :: forall e i bd c el sp. Semantics e i bd c el sp ->
              forall d g. Spine g -> Environment d e g -> sp d
lemmaSpine  sem@Semantics{..} sp rho = spine $ le <$> unSpine sp
  where le el = lemmaElim sem el rho

lemmaElim :: forall e i bd c el sp. Semantics e i bd c el sp ->
              forall d g. Elim g -> Environment d e g -> el d
lemmaElim  sem@Semantics{..} = go where
  go (App u)      rho = app $ lemmaCheck sem u rho
  go (Rec ty s z) rho = let lc t = lemmaCheck sem t rho
                        in rec (lc ty) (lc s) (lc z)


----------------------------------------------------
-- Examples of Semantics
----------------------------------------------------

renamingSemantics :: Semantics Var Infer Binder Check Elim Spine
renamingSemantics = Semantics
  { weak  = ($)
  , embed = id
  , var   = Var
  , cut   = Cut
  , ann   = Ann
  , lam   = Lam
  , piT   = Pi
  , letx  = Let
  , bnd   = \ bd t -> Bnd bd $ t (top refl) Z
  , zro   = Zro
  , suc   = Suc
  , emb   = Emb
  , nat   = Nat
  , set   = Set
  , app   = App
  , rec   = Rec
  , spine = Spine
  }

renamingCheck :: forall d g. Renaming g d -> Check g -> Check d
renamingCheck = flip (lemmaCheck renamingSemantics)

renamingInfer :: forall d g. Renaming g d -> Infer g -> Infer d
renamingInfer = flip (lemmaInfer renamingSemantics)

renamingElim :: forall d g. Renaming g d -> Elim g -> Elim d
renamingElim = flip (lemmaElim renamingSemantics)

renamingSpine :: forall d g. Renaming g d -> Spine g -> Spine d
renamingSpine = flip (lemmaSpine renamingSemantics)

-- Notice that substitution *respects* the structure of the term:
-- if a binder faces a spine, it won't fire
-- if a binder is a let, it won't fire either

substitution :: Semantics Infer Infer Binder Check Elim Spine
substitution = Semantics
  { weak  = renamingInfer
  , embed = Var
  , var   = id
  , cut   = Cut
  , ann   = Ann
  , lam   = Lam
  , piT   = Pi
  , letx  = Let
  , bnd   = \ bd t -> Bnd bd $ t (top refl) $ Var Z
  , zro   = Zro
  , suc   = Suc
  , emb   = Emb
  , nat   = Nat
  , set   = Set
  , app   = App
  , rec   = Rec
  , spine = Spine
  }

newtype Name         (g :: Context) = Name         { runName         :: String }
newtype Printer      (g :: Context) = Printer      { runPrinter      :: State [String] String }
newtype NamedPrinter (g :: Context) = NamedPrinter { runNamedPrinter :: Name g -> Printer g }

printing :: Semantics Name Printer NamedPrinter Printer Printer Printer
printing = Semantics
  { weak  = const $ Name . runName
  , embed = Name . show
  , var   = Printer . return . runName
  , cut   = \ i sp -> Printer $ do
            txti  <- runPrinter i
            txtsp <- runPrinter sp
            return $ txti ++ " " ++ txtsp
  , ann   = \ c ty -> Printer $ do
            txtc  <- runPrinter c
            txtty <- runPrinter ty
            return $ "(" ++ txtc ++ " : " ++ txtty ++ ")"
  , lam   = NamedPrinter $ \ n -> Printer $ return $ "\\" ++ runName n ++ ". "
  , piT   = \ c -> NamedPrinter $ \ n -> Printer $ do
            txtc <- runPrinter c
            return $ "(" ++ runName n ++ " : " ++ txtc ++ ") -> "
  , letx  = \ i -> NamedPrinter $ \ n -> Printer $ do
            txti <- runPrinter i
            return $ "let " ++ runName n ++ " = " ++ txti ++ "\nin "
  , bnd   = \ bd c -> Printer $ do
            (n : ns) <- get
            ()       <- put ns
            let x = Name n
            txtbd    <- runPrinter $ runNamedPrinter bd x
            txtc     <- runPrinter $ c refl x
            return $ txtbd ++ txtc
  , zro   = Printer $ return "0"
  , suc   = \ n -> Printer $ do
            txtn <- runPrinter n
            return $ "1+ " ++ txtn
  , emb   = id
  , nat   = Printer $ return "Nat"
  , set   = Printer $ return "Set"
  , app   = Printer . fmap (\ txt -> "(" ++ txt ++ ")") . runPrinter
  , rec   = \ ty s z -> Printer $ do
            txtty <- runPrinter ty
            txts  <- runPrinter s
            txtz  <- runPrinter z
            return $ "Rec[" ++ txtty ++ "](" ++ txts ++ ", " ++ txtz ++ ")"
  , spine = flip foldr (Printer $ return "")
            $ \ hd tl -> Printer $ do
            txthd <- runPrinter hd
            txttl <- runPrinter tl
            return $ txthd ++ " " ++ txttl

  }

initNames :: forall g. SContextI g => State [String] (Environment g Name g)
initNames = go witness where
  go :: forall g'. SContext g' -> State [String] (Environment g Name g')
  go SNull     = return Context.null
  go (SBind g) = do
    (n : ns) <- get
    ()       <- put ns
    rho      <- go g
    return $ rho `cons` Name n

freshNames :: [String]
freshNames = fmap (:[]) alpha ++ alphaInt where
  alpha    = ['a'..'z']
  alphaInt = concat $ fmap (\ i -> fmap (: show i) alpha) [(0 :: Integer)..]

instance SContextI g => Show (Check g) where
  show c = flip evalState freshNames $ do
           rho <- initNames
           runPrinter $ lemmaCheck printing c rho

instance SContextI g => Show (Infer g) where
  show i = flip evalState freshNames $ do
           rho <- initNames
           runPrinter $ lemmaInfer printing i rho


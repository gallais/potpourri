{-# OPTIONS -Wall                  #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE EmptyCase             #-}
{-# LANGUAGE ScopedTypeVariables   #-}

module Syntaxes where

import Data.Function
import Data.Proxy
import Data.Functor.Classes
import Control.Newtype
import Control.Monad.Reader
import Control.Monad.State

import Utils
import Scopes
import Generic

-------------------------------------------------------------
-- UNTYPED LAMBDA CALCULUS
-------------------------------------------------------------

type Term = Fix' TmF Scope'

data TmF (r :: ((* -> *) -> (* -> *)) -> (* -> *))
         (s :: (* -> *) -> (* -> *))
         (a :: *)
         :: * where
  L :: s (r s) a      -> TmF r s a -- Lambda Abstraction
  A :: r s a -> r s a -> TmF r s a -- Application

instance SyntaxWithBinding TmF where
  reindex fs fs' r s e = case e of
    L b   -> L $ fs' runApply $ s (over Apply) $ fs Apply b
    A f t -> A (r f) (r t)
instance Functor Term where fmap = hfmap . over Variable

pattern TmL t   = Fix (L t)
pattern TmA f t = Fix (A f t)

pattern TmL' t   = Fix (L (Scope t))
-------------------------------------------------------------
-- UNTYPED LAMBDA CALCULUS WITH UNIT, SUMS, AND FIXPOINTS
-------------------------------------------------------------

type Case = Fix' CsF Scope'

data CsF (r :: ((* -> *) -> (* -> *)) -> (* -> *))
         (s :: (* -> *) -> (* -> *))
         (a :: *)
         :: * where
  LI :: r s a -> CsF r s a                     -- Left  Injection
  RI :: r s a -> CsF r s a                     -- Right Injection
  CA :: r s a -> s (Pair (r s)) a -> CsF r s a -- Case  Analysis
  FX :: s (r s) a -> CsF r s a                 -- Fixpoint Operator
  LA :: s (r s) a -> CsF r s a                 -- Lambda Abstraction
  AP :: Pair (r s) a -> CsF r s a              -- Application
  UN :: CsF r s a                              -- Unit

instance SyntaxWithBinding CsF where
  reindex fs fs' r s e = case e of
    LI t   -> LI $ r t
    RI t   -> RI $ r t
    CA c b -> CA (r c) $ s pair b
    FX f   -> FX $ fs' runApply $ s (over Apply) $ fs Apply f
    LA b   -> LA $ fs' runApply $ s (over Apply) $ fs Apply b
    AP p   -> AP $ pair r p
    UN     -> UN

instance Functor Case where fmap = hfmap . over Variable

pattern CsLI t   = Fix (LI t)
pattern CsRI t   = Fix (RI t)
pattern CsCA t b = Fix (CA t b)
pattern CsFX f   = Fix (FX f)
pattern CsLA f   = Fix (LA f)
pattern CsAP f t = Fix (AP (Pair (f, t)))
pattern CsUN     = Fix UN

pattern CsCA' t b = Fix (CA t (Scope b))
pattern CsFX' f   = Fix (FX (Scope f))
pattern CsLA' f   = Fix (LA (Scope f))

($$) :: Case a -> Case a -> Case a
($$) f t = CsAP f t


-------------------------------------------------------------
-- MINI TT
-------------------------------------------------------------


type TT = Fix Fin TTF (Scope Fin)

data TTF (r :: ((Natural -> *) -> (Natural -> *)) -> (Natural -> *))
         (s :: (Natural -> *) -> (Natural -> *))
         (a :: Natural)
         :: * where
  PI   :: r s a -> s (r s) a -> TTF r s a
  LM   :: s (r s) a -> TTF r s a
  (:$) :: r s a -> r s a -> TTF r s a

instance SyntaxWithBinding TTF where
  reindex fs fs' r s e = case e of
    PI a b -> PI (r a) $ fs' runApply $ s (over Apply)  $ fs Apply b
    LM b   -> LM $ fs' runApply $ s (over Apply) $ fs Apply b
    f :$ t -> ((:$) `on` r) f t

pattern TTPI a b = Fix (PI a b)
pattern TTLM b   = Fix (LM b)
pattern TTAP f t = Fix (f :$ t)

-------------------------------------------------------------
-- CYCLIC LISTS
-------------------------------------------------------------

data CLF (e :: *) -- element type
         (r :: ((Natural -> *) -> (Natural -> *)) -> (Natural -> *))
         (s :: (Natural -> *) -> (Natural -> *))
         (a :: Natural)
         :: * where
  NIL  :: CLF e r s a
  (:<) :: e -> s (r s) a -> CLF e r s a

type CL e = Fix Fin (CLF e) (Scope Fin)

instance SyntaxWithBinding (CLF e) where
  reindex fs fs' _ s e = case e of
    NIL      -> NIL
    hd :< tl -> hd :< (fs' runApply $ s (over Apply) $ fs Apply tl)

pattern CLNIL       = Fix NIL
pattern CLCON  e es = Fix (e :< es)
pattern CLCON' e es = CLCON e (Scope es)

instance Alg Fin (CLF e) (CONST [e]) (CONST [e]) where
  ret _ _ = id
  alg _ e = case e of
    NIL      -> CONST []
    hd :< tl -> let prfx :: CONST [e] ~> CONST [e]
                    prfx = over CONST (hd :)
                in prfx $ fixpoint' prfx $ kripke runConst tl

toStream :: forall e. CList e -> [e]
  -- contracting this type signature using ~> takes `e` out
  -- of scope which makes it impossible to mention it in the
  -- proxy type in the body of the function!
toStream = runCONST . eval' (Proxy :: Proxy (CONST [e])) finZero . runCList

instance MonadReader (e -> f) m => Alg Fin (CLF e) Fin (Compose m (CL f)) where
  ret _ _ = Compose . return . Var
  alg _ e = Compose $ case e of
    NIL      -> return CLNIL
    hd :< tl ->
      let hd' = fmap ($ hd) ask
          tl' = fmap Scope $ runCompose $ runScope $ abstract' id tl
      in CLCON <$> hd' <*> tl'

newtype CList a = CList { runCList :: CL a 'Zero }

instance Newtype (CList a) (CL a 'Zero) where
  pack = CList
  unpack = runCList

instance Functor CList where
  fmap f = over CList $ ($ f) . runCompose . eval' (Proxy :: Proxy Fin) finZero

-------------------------------------------------------------
-- ALGEBRAS FOR NORMALISATION BY EVALUATION
-------------------------------------------------------------

instance Alg Variable TmF (Model Variable TmF) (Model Variable TmF) where
  ret _ _ = id
  alg _ e = case e of
    L b   -> Model $ Fix $ L $ kripke (runModel . runConst) b
    A f t -> case runModel (runConst t) of
      Fix (L b) -> Model $ runKripke b id (runConst t)
      _         -> Model $ Fix $ (A `on` runModel . runConst) f t

instance Alg Variable CsF (Model Variable CsF) (Model Variable CsF) where
  ret _ _ = id
  alg _ e =
    let cleanup = runModel . runConst
    in case e of
    LI t    -> Model $ Fix $ LI $ cleanup t
    RI t    -> Model $ Fix $ RI $ cleanup t
    CA f kp -> case cleanup f of
      CsLI l -> runConst $ first  $ runKripke kp id $ Model l 
      CsRI r -> runConst $ second $ runKripke kp id $ Model r
      f'     -> Model $ Fix $ CA f' $ kripke (pair cleanup) kp
    FX kp   -> fixpoint $ kripke runConst kp
    LA b    -> Model $ Fix $ LA $ kripke cleanup b
    AP p    -> Model $ case cleanup (first p) of
      Fix (LA b) -> runKripke b id (runConst $ second p)
      _          -> Fix $ AP $ pair cleanup p    
    UN      -> Model $ Fix UN      

instance HigherFunctor Variable (Fix' TmF (Kripke' (Model' f))) where
  hfmap f e = case e of
    Var a  -> Var (f a)
    Fix e' -> Fix $ case e' of
      L b   -> L $ hfmap f b
      A t u -> (A `on` hfmap f) t u

instance HigherFunctor Variable (Fix' CsF (Kripke' (Model' CsF))) where
  hfmap f e = case e of
    Var a  -> Var $ f a
    Fix e' -> Fix $ case e' of
      LI t    -> LI $ hfmap f t
      RI t    -> RI $ hfmap f t
      CA t kp -> CA (hfmap f t) $ hfmap f kp
      FX kp   -> FX $ hfmap f kp
      LA kp   -> LA $ hfmap f kp
      AP p    -> AP $ hfmap f p
      UN      -> UN

-------------------------------------------------------------
-- SHOW INSTANCES
-------------------------------------------------------------

instance (Show1 (r s), Show1 (s (r s))) => Show1 (TmF r s) where
  showsPrec1 i e = case e of
    L b   -> showString "L " . showsPrec1 (1+i) b
    A f t -> showsBinary1 "A" i f t

deriving instance (Show (r s a), Show (s (r s) a)) => Show (TmF r s a)


instance (MonadState [String] m, Show e) => Alg Fin (CLF e) (CONST String) (Compose m (CONST String)) where
  ret _ _ = Compose . return
  alg _ e = Compose $ case e of
    NIL      -> return $ CONST "NIL"
    hd :< tl -> do
      (nm : rest) <- get
      put rest
      str <- runCompose $ runScope $ abstract' (const $ CONST nm) tl
      return $ over CONST ((concat ["fix ", nm, ". ", show hd, " :< "]) ++) str

-- Trick to avoid the overlapping instance with `Fix ...` declared
-- generically a bit earlier
instance Show e => Show (Apply (CL e) n) where
  show e = case runApply e of
    Var a       -> "Var " ++ show a
    CLNIL       -> "NIL"
    CLCON hd tl -> show hd ++ " :< " ++ show (Apply $ runScope tl)

instance Show e => Show (CList e) where
  show = show . Apply . runCList

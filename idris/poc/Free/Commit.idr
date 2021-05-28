module Free.Commit

import Data.List
import Data.List1
import Data.Maybe
import Data.DPair
import Free.Common

%default total

data Free : Pred Type -> Pred Type
BCont : Pred Type -> Rel Type

data Free : Pred Type -> Pred Type where
  Pure   : a -> Free m a
  Lift   : m a -> Free m a
  Commit : Free m ()
  Must   : Free m a -> Free m a
  Alts   : List (Free m a) -> Free m a
  Bind   : Free m a -> BCont m a b -> Free m b

BCont m = Bwd (Kleisli (Free m))

bind : Free m a -> (a -> Free m b) -> Free m b
bind (Pure a)   f = f a
bind (Bind m k) f = Bind m (k :< f)
bind (Alts [])  f = Alts []
bind m          f = Bind m (BNil :< f)

Functor (Free m) where
  map f t = bind t (Pure . f)

Applicative (Free m) where
  pure = Pure
  fs <*> xs = bind fs $ \ f => map (f $) xs

Monad (Free m) where
  (>>=) = bind

fail : Free m a
fail = Alts []

-- We can't do the same fusion anymore as that would change the
-- meaning of `commit`. (<|>) associates to the right only.
union : Free m a -> Free m a -> Free m a
union m@(Pure _) n = m
union m@(Lift _) n = m
union m@Commit   n = m
union m (Alts ns) = Alts (m :: ns)
union m n = Alts [m,n]

Alternative (Free m) where
  empty = fail
  m <|> n = union m n

FCont : Pred Type -> Rel Type
FCont m = Fwd1 (Kleisli (Free m))

data Stack : Pred Type -> Rel Type where
  Empty : Stack m i i
  Hdls  : List (List1 (Free m i)) -> Stack m i j -> Stack m i j
  Cont  : Fwd1 (FCont m) i j -> Stack m j k -> Stack m i k

filterHdls : Stack m i j -> Bwd (Fwd1 (FCont m)) i j
filterHdls = go BNil where

  go : Bwd (Fwd1 (FCont m)) x y -> Stack m y z -> Bwd (Fwd1 (FCont m)) x z
  go acc Empty = acc
  go acc (Hdls _ stk) = go acc stk
  go acc (Cont fs stk) = go (acc :< fs) stk

flatten : Stack m i j -> Stack m i j
flatten stk = case filterHdls stk of
  BNil => Empty
  fss :< fs => Cont (concat (fss :< fs)) Empty

push : Fwd (Kleisli (Free m)) i j -> Stack m j k -> Stack m i k
push FNil      stk                  = stk
push (f :> fs) (Cont (k :> ks) stk) = Cont ((f :> fs) :> (k :> ks)) stk
push (f :> fs) stk                  = Cont ((f :> fs) :> FNil) stk

cont : Fwd (FCont m) i j -> Stack m j k -> Stack m i k
cont FNil stk = stk
cont (fs :> fss) stk = Cont (fs :> fss) stk

-- can't do any optimisation here because of commit
install : List (Free m i) -> Stack m i j -> Stack m i j
install [] = Hdls []
install (m :: ms) = Hdls [m ::: ms]

uninstall : Stack m i j -> Stack m i j
uninstall (Hdls ns stk) = Hdls [] stk
uninstall (Cont fs (Hdls ns stk)) = Cont fs (Hdls [] stk)
  -- not pushing so that multiple commits do not start cancelling surrounding actions!
uninstall stk = stk

hdls : List (List1 (Free m i)) -> Stack m i j -> Stack m i j
hdls = Hdls

namespace List1

  export
  first : List (List1 a) -> Maybe (a, List (List1 a))
  first [] = Nothing
  first ((m ::: []) :: mss) = pure (m, mss)
  first ((m ::: (n :: ns)) :: mss) = pure (m, (n ::: ns) :: mss)

namespace Fwd1

  export
  first : Fwd1 (Fwd1 r) i k -> Exists \ j =>
          (r i j, Fwd (Fwd1 r) j k)
  first ((k :> FNil) :> kss) = Evidence _ (k, kss)
  first ((k :> (l :> ls)) :> kss) = Evidence _ (k, (l :> ls) :> kss)

homo : Monad n =>
       ({0 a : Type} ->      m a -> n        a) ->
       ({0 a : Type} -> Free m a -> n (Maybe a))
homo f t = free t Empty where

  free     : Free m i -> Stack m i j -> n (Maybe j)
  continue : i        -> Stack m i j -> n (Maybe j)
  handle   :             Stack m i j -> n (Maybe j)

  free (Pure a)         stk = continue a stk
  free (Lift m)         stk = f m >>= \ x => continue x stk
  free Commit           stk = continue () (uninstall stk)
  free (Must m)         stk = free m (flatten stk)
  free (Alts [])        stk = handle stk
  free (Alts (m :: ms)) stk = free m (install ms stk)
  free (Bind m f)       stk = free m (push (reverse f) stk)

  continue a Empty          = pure (Just a)
  continue a (Hdls _   stk) = continue a stk
  continue a (Cont kss stk) = case first kss of
    (Evidence _ (k, kss)) => assert_total $ free (k a) (cont kss stk)

  handle Empty          = pure Nothing
  handle (Cont _   stk) = handle stk
  handle (Hdls mss stk) = case first mss of
    Just (m, mss) => assert_total $ free m (hdls mss stk)
    Nothing => handle stk

--------------------------------------------------------------
-- Example

data Eff : Type -> Type where
  Get      : Eff Nat
  PutStrLn : String -> Eff ()

eff : Eff a -> IO a
eff = \case
  Get          => length <$> getLine
  (PutStrLn x) => putStrLn x

putStrLn : String -> Free Eff ()
putStrLn = Lift . PutStrLn

error : String -> Free Eff a
error err = do
  putStrLn err
  fail

guard : Bool -> Free Eff ()
guard b = if b then Pure () else fail

printInput : Free Eff ()
printInput = do
  putStrLn "Input"
  n <- Lift Get
  guard (n /= Z)
  Commit -- if we get one valid output, they better all be valid!
  putStrLn (show n)

prog : Free Eff ()
prog = sequence_ (replicate 3 printInput)
   <|> error "Failed!"
   <|> putStrLn "Ouch: error in the error handler!"
   <|> putStrLn "This better not show up!"

echo : Nat -> Free Eff Nat
echo n = do
  putStrLn ("Passing " ++ show n)
  pure n

nested : Free Eff ()
nested = do n <- (error "Not here" <|> echo Z <|> echo (S Z))
            if n /= Z
              then putStrLn (show n)
              else error "No backtracking in the first bind"

doubleCommit : Free Eff ()
doubleCommit
  = ((putStrLn "hello" *> Commit *> Commit *> fail) <|> putStrLn "bypassed")
    <|> putStrLn "world" -- success
    <|> putStrLn "unreachable"

outsideMust : Free Eff ()
outsideMust = (<|> putStrLn "No gonnae do that") $
  do putStrLn "hello"
     Must (fail <|> putStrLn "world")
     Must fail <|> putStrLn "unreachable"

run : Free Eff () -> IO ()
run prog = ignore $ homo eff prog

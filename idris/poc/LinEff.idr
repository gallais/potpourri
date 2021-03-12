module LinEff

import System.File
import Control.Linear.LIO

Res : List Type -> Type
Res [] = ()
Res (a :: as) = LPair a (Res as)

interface Member (0 t : Type) (0 ts : List Type) where
  0 Leftovers' : List Type
  remove : (1 _ : Res ts) -> LPair t (Res Leftovers')
  insert : (1 _ : LPair t (Res Leftovers')) -> Res ts

0 Leftovers : (0 t : Type) -> (0 ts : List Type) -> Member t ts => List Type
Leftovers t ts @{p} = Leftovers' @{p}

Member t (t :: ts) where
  Leftovers' = ts
  remove vs = vs
  insert vs = vs

Member t ts => Member t (u :: ts) where
  Leftovers' = u :: Leftovers t ts
  remove (v # vs) = let (r # vs) = remove vs in (r # (v # vs))
  insert (r # (v # vs)) = (v # insert (r # vs))

data M : List Type -> List Type -> Type -> Type where
  Pure : a -> M res res a
  Lift : IO a -> M res res a
  Bind : M res1 res2 a -> (a -> M res2 res3 b) -> M res1 res3 b
  With : (r : Type) -> Member r res1 =>
         (1 f : (1 _ : r) -> M (Leftovers r res1) res2 a) ->
         M res1 res2 a
  Put : (1 _ : r) -> M res (r :: res) ()
  Back : Member r res => (1 _ : r) -> M (Leftovers r res) res ()

(>>=) : M res1 res2 a -> (a -> M res2 res3 b) -> M res1 res3 b
(>>=) = Bind

(>>) :  M res1 res2 () -> M res2 res3 b -> M res1 res3 b
m >> n = Bind m (\ () => n)

pure : a -> M res res a
pure = Pure

namespace Handle

  export
  data Handle : String -> Type where
    MkHandle : File -> Handle fp

  export
  partial
  openFile : (fp : String) -> (m : Mode) -> M res (Handle fp :: res) ()
  openFile fp m = do
    Right rawH <- Lift (openFile fp m)
    Put (MkHandle rawH)
    Pure ()

  export
  partial
  readLine: (fp : String) -> Member (Handle fp) res => M res res String
  readLine fp = do
    With (Handle fp) $ \(MkHandle rawH) => do
      Right str <- Lift (fGetLine rawH)
      Back (MkHandle rawH)
      Pure str

  export
  partial
  closeFile : (fp : String) -> Member (Handle fp) res =>
              M res (Leftovers (Handle fp) res) ()
  closeFile fp = do
    With (Handle fp) $ \ (MkHandle rawH) => Lift (closeFile rawH)

public export
EFF : Type -> Type
EFF = M [] []

partial
firstLine : (fp : String) -> EFF String
firstLine fp = do
  openFile fp Read
  str <- readLine fp
  closeFile fp
  pure str

runM : LinearIO io =>
       (1 m : M res1 res2 a) -> (1 vs : Res res1) ->
       (1 k : (1 ws : Res res2) -> a -> L io b) -> L io b
runM (Pure a) vs k = k vs a
runM (Lift io) vs k = k vs !(liftIO io)
runM (Bind m f) vs k = runM m vs (\ ws, a => runM (f a) ws k)
runM (With r f) vs k =
  let (r # ws) = remove vs in
  runM (f r) ws k
runM (Put r) vs k = k (r # vs) ()
runM (Back r) vs k = k (insert (r # vs)) ()

runEFF : (1 e : EFF a) -> IO a
runEFF m = run (runM m () (\ (), a => pure a))

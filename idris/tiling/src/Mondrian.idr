module Mondrian

import Data.Fin
import Data.Matrix
import Data.Nat
import Data.Relation.Binary
import Data.Tiling
import Data.Vect
import NCurses

import System.Random

0 Painting : Sized
Painting = Tiling (\_,_ => Color)

CFG : Config
CFG = MkConfig
  { noDelayEnabled = False
  , keypadEnabled  = False
  , colorEnabled   = True
  }

colorToFin : Color -> Fin 8
colorToFin Black = 0
colorToFin Red = 1
colorToFin Green = 2
colorToFin Yellow = 3
colorToFin Blue = 4
colorToFin Magenta = 5
colorToFin Cyan = 6
colorToFin White = 7

allColors : Vect 8 Color
allColors = [Black, Red, Green, Yellow, Blue, Magenta, Cyan, White]

Random Bool where
  randomIO = (0 ==) <$> randomRIO (0, the Int32 1)
  randomRIO (False, True) = randomIO
  randomRIO (b, _) = pure b

-- The bound better be smaller than MAX_INT32
randNat : Nat -> IO Nat
randNat bnd = do let i : Int32 = !randomIO
                 pure $ cast (abs i `mod` cast bnd)

randFin : (n : Nat) -> {auto 0 _ : NonZero n} -> IO (Fin n)
randFin (S n) = do k <- randNat (S n)
                   pure (restrict n $ cast k)

-- For a Mondrian painting we don't use all of the colours
randColor : IO Color
randColor = pure $ case !(randFin 8) of
  0 => Blue
  1 => Yellow
  2 => Red
  _ => White

solid : {w, h : Nat} -> IO (Painting w h)
solid = pure $ Value !randColor

mondrian : {w, h : Nat} -> IO (Painting w h)
vcut     : {w, h : Nat} -> IO (Painting w h)
hcut     : {w, h : Nat} -> IO (Painting w h)

mondrian =
  if w <= 20 || h <= 15
    then solid
  else if w >= 50 || h >= 20
    then do r <- randomRIO (0,the Int32 20)
            if r <= 10 then vcut else hcut
  else do r <- randomRIO (0, the Int32 25)
          if r <= 10
            then vcut
            else if r <= 20 then hcut else solid

vcut
  = do b <- (0 /=) <$> randomRIO (0, the Int32 5)
       let leftover = ifThenElse b pred id h
       ht <- cast <$> randomRIO (the Int32 2, cast leftover - 2)
       let hb = leftover `minus` ht
       top <- mondrian {w, h = ht}
       bot <- mondrian {w, h = hb}
       let bb : Painting w (ifThenElse b (S hb) hb)
              = if b
                   then Value {h = 1} Black
                        ~~~~
                        bot
                   else bot
       pure $ believe_me
            $ top
              ~~~~
              bb

hcut
  = do b <- (0 /=) <$> randomRIO (0, the Int32 5)
       let leftover = ifThenElse b pred id w
       wl <- cast <$> randomRIO (the Int32 4, cast leftover - 4)
       let wr = leftover `minus` wl
       left <- mondrian {w = wl, h}
       right <- mondrian {w = wr, h}
       let br : Painting (ifThenElse b (S wr) wr) h
              = if b then Value {w = 1} Black |~~| right else right
       pure $ believe_me $ left |~~| br

paint : (enc : Color -> ColorPair) ->
        {w, h : Nat} -> Position -> Painting w h -> NCurses CFG CFG ()
paint enc pos Empty     = pure ()
paint enc pos (Value c)
  = do nSetAttr (CP $ enc c)
       for_ @{NCURSES} [0..pred h] $ \ i =>
         mvHLine ({ row $= (i +) } pos) ' ' w
paint enc pos (Layer l) = case l of
  SplitH {wl, wr} prf l r => do paint enc pos l
                                paint enc ({ col $= (wl+) } pos) r
  SplitV {ht, hb} prf t b => do paint enc pos t
                                paint enc ({ row $= (ht+) } pos) b

loop : (enc : Color -> ColorPair) -> NCurses CFG CFG ()
wait : (enc : Color -> ColorPair) -> NCurses CFG CFG ()

wait enc = case !getCh of
  'r' => loop enc
  'q' => pure ()
  _ => wait enc

loop enc = do
  sz <- getSize
  pic <- lift $ mondrian { w = sz.width, h = sz.height }
  paint enc (MkPosition Z Z) pic
  wait enc

main : IO ()
main = runNCurses $ NCurses.do
  noEcho
  startColor

  cs <- for @{NCURSES} allColors $ \ k =>
           initColorPair (cast (colorToFin k)) k k
  let enc = flip index cs . colorToFin

  loop enc

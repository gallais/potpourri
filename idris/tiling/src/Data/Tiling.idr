module Data.Tiling

import Data.Display
import Data.Either
import Data.Nat
import Data.Relation.Binary
import Data.These

%default total

public export
data Split : Sized -> Sized where
  SplitH : {0 t : Sized} ->
           {wl, wr : Nat} -> (0 _ : w === wl + wr) ->
           t wl h -> t wr h -> Split t w h
  SplitV : {0 t : Sized} ->
           {ht, hb : Nat} -> (0 _ : h === ht + hb) ->
           t w ht -> t w hb -> Split t w h

public export
data Tiling : Sized -> Sized where
  Empty : Tiling t w h
  Value : {0 t : Sized} -> t w h -> Tiling t w h
  Layer : Split (Tiling t) w h -> Tiling t w h

export
layer : Split (Tiling t) w h -> Tiling t w h
layer (SplitH prf Empty Empty) = Empty
layer (SplitV prf Empty Empty) = Empty
layer spl = Layer spl

infixr 3 ||
infixr 4 ==

||| Horizontal append
export
(||) : {wl, wr : Nat} ->
       Tiling t wl h -> Tiling t wr h -> Tiling t (wl + wr) h
Empty || Empty = Empty
lft || rgt = Layer (SplitH Refl lft rgt)

||| Vertical append
export
(==) : {0 h : Nat} -> {ht, hb : Nat} ->
       Tiling t w ht -> Tiling t w hb -> Tiling t w (ht + hb)
Empty == Empty = Empty
top == bot = Layer (SplitV Refl top bot)

namespace Split

  export
  map : [ t ~> u ] -> [ Split t ~> Split u ]
  map f (SplitH prf lft rgt) = SplitH prf (f lft) (f rgt)
  map f (SplitV prf top bot) = SplitV prf (f top) (f bot)

  export
  transpose : {0 t : Sized} ->
              ({w, h : Nat} -> t w h -> t h w) ->
              ({w, h : Nat} -> Split t w h -> Split t h w)
  transpose tr (SplitH prf l r) = SplitV prf (tr l) (tr r)
  transpose tr (SplitV prf t b) = SplitH prf (tr t) (tr b)

  export
  mirror : [ Split t ~> Split t ]
  mirror (SplitH prf l r) = SplitH (trans prf $ plusCommutative _ _) r l
  mirror (SplitV prf b t) = SplitV (trans prf $ plusCommutative _ _) t b

namespace Tiling

  export
  map : [ t ~> u ] -> [ Tiling t ~> Tiling u ]
  map f Empty     = Empty
  map f (Value v) = Value (f v)
  map f (Layer l) = layer $ assert_total $ map (map f) l

  export
  bind : [ t ~> Tiling u ] -> [ Tiling t ~> Tiling u ]
  bind f Empty     = Empty
  bind f (Value v) = f v
  bind f (Layer l) = layer $ assert_total $ map (bind f) l

  export
  join : [ Tiling (Tiling t) ~> Tiling t ]
  join = bind id

  export
  transpose : {0 t : Sized} ->
              ({w, h : Nat} -> t w h -> t h w) ->
              ({w, h : Nat} -> Tiling t w h -> Tiling t h w)
  transpose tr Empty     = Empty
  transpose tr (Value v) = Value (tr v)
  transpose tr (Layer l) = Layer (assert_total $ transpose (transpose tr) l)

  export
  mirror : [ Tiling t ~> Tiling t ]
  mirror Empty     = Empty
  mirror (Value v) = Value v
  mirror (Layer l) = Layer $ mirror $ assert_total $ map mirror l

public export
interface Cutting (0 t, u : Sized) | t where
  splitH : {wl, wr : Nat} -> (0 _ : w === wl + wr) ->
           t w h -> (u wl h, u wr h)
  splitV : {ht, hb : Nat} -> (0 _ : h === ht + hb) ->
           t w h -> (u w ht, u w hb)

||| We assume here that we represent a point in a segment of
||| size w by two values l and r and a proof that l+r === w.
|||
||| Given two points, produce a Cut that shows their position
||| relative to each other.
data Cut : (l1, r1, l2, r2 : Nat) -> Type where
  ||| l1 is to the left of l2
  ||| <- l1 -><------ r1 ----->
  ||| <---- l2 -----><-- r2 -->
  |||
  ||| We get a small segment m in between l1 and r2:
  |||
  |||         <------ r1 ----->
  ||| <- l1 -><- m -><-- r2 -->
  ||| <---- l2 ----->
  Left : (m : Nat) ->
         r1 === m + r2 ->
         l2 === l1 + m ->
         Cut l1 r1 l2 r2
  ||| Both splits are the same
  ||| <- l1 -><------ r1 ----->
  ||| <- l2 -><------ r2 ----->
  Same : l1 === l2 -> r1 === r2 -> Cut l1 r1 l2 r2
  ||| l1 is to the right of l2
  ||| <---- l1 -----><-- r1 -->
  ||| <- l2 -><------ r2 ----->
  |||
  ||| We get a small segment m in between l2 and r1:
  |||
  |||         <------ r2 ----->
  ||| <- l2 -><- m -><-- r1 -->
  ||| <---- l1 ----->
  Right : (m : Nat) ->
         l1 === l2 + m ->
         r2 === m + r1 ->
         Cut l1 r1 l2 r2

cut : {l1, r1, l2, r2 : Nat} ->
      (0 _ : w === l1 + r1) ->
      (0 _ : w === l2 + r2) ->
      Cut l1 r1 l2 r2
cut {l1 = 0}    {l2 = 0}    eq1 eq2
  = Same Refl (trans (sym eq1) eq2)
cut {l1 = 0}    {l2 = S l2} eq1 eq2
  = Left (S l2) (trans (sym eq1) eq2) Refl
cut {l1 = S l1} {l2 = 0}    eq1 eq2
  = Right (S l1) Refl (trans (sym eq2) eq1)
cut {l1 = S l1} {l2 = S l2} Refl eq2
  with (cut {l1} {l2} Refl (succInjective _ _ eq2))
  _ | (Left  m prf1 prf2) = Left m prf1 (cong S prf2)
  _ | (Same    prf1 prf2) = Same (cong S prf1) prf2
  _ | (Right m prf1 prf2) = Right m (cong S prf1) prf2

export
[LIFT] Cutting t u => Cutting t (Tiling u) where
  splitH prf t = bimap Value Value $ splitH prf t
  splitV prf t = bimap Value Value $ splitV prf t

export
[SPLIT] Cutting t (Tiling u) =>
  Cutting (Split t) (Tiling (lift 2 Either t (Tiling u))) where
  splitH prf (SplitH prfH lft rgt) with (cut prf prfH)
    _ | Left  m prf1 prf2 =
        let (lftlft, lftrgt) = splitH prf2 lft in
        ( Value $ Right lftlft
        , Layer $ SplitH prf1 (Value $ Right lftrgt)
                              (Value $ Left rgt)
        )
    _ | Same    Refl Refl = (Value $ Left lft, Value $ Left rgt)
    _ | Right m prf1 prf2 =
        let (rgtlft, rgtrgt) = splitH prf2 rgt in
        ( Layer $ SplitH prf1 (Value $ Left lft)
                              (Value $ Right rgtlft)
        , Value $ Right rgtrgt
        )
  splitH prf (SplitV prfV top bot)
    = let (topL, topR) = splitH prf top
          (botL, botR) = splitH prf bot
      in ( Layer $ SplitV prfV (Value $ Right topL)
                               (Value $ Right botL)
         , Layer $ SplitV prfV (Value $ Right topR)
                               (Value $ Right botR)
         )

  splitV prf (SplitH prfH lft rgt)
    = let (lftT, lftB) = splitV prf lft
          (rgtT, rgtB) = splitV prf rgt
      in ( Layer $ SplitH prfH (Value $ Right lftT)
                               (Value $ Right rgtT)
         , Layer $ SplitH prfH (Value $ Right lftB)
                               (Value $ Right rgtB)
         )
  splitV prf (SplitV prfV top bot) with (cut prf prfV)
    _ | Left  m prf1 prf2 =
        let (toptop, topbot) = splitV prf2 top in
        ( Value $ Right toptop
        , Layer $ SplitV prf1 (Value $ Right topbot)
                              (Value $ Left bot))
    _ | Same    Refl Refl = (Value $ Left top, Value $ Left bot)
    _ | Right m prf1 prf2 =
        let (bottop, botbot) = splitV prf2 bot in
        ( Layer $ SplitV prf1 (Value $ Left top) (Value $ Right bottop)
        , Value $ Right botbot
        )

export
Cutting t (Tiling t) => Cutting (Tiling t) (Tiling t) where
  splitH prf Empty     = (Empty, Empty)
  splitH prf (Value v) = splitH prf v
  splitH prf (Layer l)
    = bimap (bind fromEither) (bind fromEither)
    $ assert_total $ splitH prf @{SPLIT} l

  splitV prf Empty     = (Empty, Empty)
  splitV prf (Value v) = splitV prf v
  splitV prf (Layer l)
    = bimap (bind fromEither) (bind fromEither)
    $ assert_total $ splitV @{SPLIT} prf l

namespace Split

  export
  mergeWith : Cutting u u =>
              [       t ~> u ~>       v ] ->
              [ Split t ~> u ~> Split v ]
  mergeWith f (SplitH prf lft rgt) u
    = let (ulft, urgt) = splitH prf u in
      SplitH prf (f lft ulft) (f rgt urgt)
  mergeWith f (SplitV prf top bot) u
    = let (utop, ubot) = splitV prf u in
      SplitV prf (f top utop) (f bot ubot)

namespace Tiling

  ||| Merge two screens into one
  ||| * Empty acts as a transparent layer
  |||
  ||| To destructively stack a screen on top of another one
  ||| instead, see `stackWith`
  export
  mergeWith : Cutting t (Tiling t) => Cutting u (Tiling u) =>
              [ (lift 2 These) t u ~> v ] ->
              [ Tiling t ~> Tiling u ~> Tiling v ]
  mergeWith f Empty     bot       = map (f . That) bot
  mergeWith f top       Empty     = map (f . This) top
  mergeWith f (Value v) (Value w) = Value (f (Both v w))
  mergeWith f (Layer l) bot       =
    layer $ assert_total $ mergeWith (mergeWith f) l bot
  mergeWith f top       (Layer l) =
    layer $ assert_total $ mergeWith (mergeWith (f . swap)) l top

  ||| Stack the first screen on top of the second.
  ||| * Empty acts as a transparent layer
  ||| * Value acts as fully opaque
  export
  stackWith : Cutting u (Tiling u) =>
              [ (lift 2 Either) t u ~> v ] ->
              [ Tiling t ~> Tiling u ~> Tiling v ]
  stackWith f Empty     bot   = map (f . Right) bot
  stackWith f top       Empty = map (f . Left) top
  stackWith f (Value v) bot   = Value (f (Left v))
  stackWith f (Layer l) bot   =
    layer $ assert_total $ mergeWith (stackWith f) l bot

-- TODO: diff as a mergeWith!

export
Display t => Display (Split t) where
  displayAt pos (SplitH {wl} prf l r)
    = displayAt pos l ++ displayAt ({ colnNo $= (wl +) } pos) r
  displayAt pos (SplitV {ht} prf t b)
    = displayAt pos t ++ displayAt ({ lineNo $= (ht +) } pos) b

export
Display t => Display (Tiling t) where
  displayAt pos Empty     = []
  displayAt pos (Value v) = displayAt pos v
  displayAt pos (Layer l) = assert_total $ displayAt pos l

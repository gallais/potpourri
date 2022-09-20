module CSE

import Control.Function
import Decidable.Equality
import Data.SnocList
import Data.SnocList.Quantifiers
import Data.List1
import Data.Maybe
import Data.String
import Data.Stream

%default total

namespace Thinning

  public export
  data Thinning : (sx, sy : SnocList a) -> Type where
    Done : Thinning [<] [<]
    Keep : Thinning sx sy -> (0 x : a) -> Thinning (sx :< x) (sy :< x)
    Drop : Thinning sx sy -> (0 x : a) -> Thinning sx (sy :< x)

  %name Thinning th, ph

  infixr 8 <.>
  export
  (<.>) : Thinning sx sy -> Thinning sy sz -> Thinning sx sz
  th <.> Done = th
  Keep th x <.> Keep ph x = Keep (th <.> ph) x
  Drop th x <.> Keep ph x = Drop (th <.> ph) x
  th <.> Drop ph x = Drop (th <.> ph) x

  export
  (<+>) : Thinning sx sy -> Thinning sa sb ->
          Thinning {a} (sx <+> sa) (sy <+> sb)
  th <+> Done = th
  th <+> (Keep ph x) = Keep (th <+> ph) x
  th <+> (Drop ph x) = Drop (th <+> ph) x

  export
  Drops : Thinning sx sy -> (sa : SnocList a) -> Thinning sx (sy <+> sa)
  Drops th [<] = th
  Drops th (sz :< x) = Drop (Drops th sz) x

namespace Cover

  public export
  data Cover : (th : Thinning {a} sx1 sy) -> (ph : Thinning sx2 sy) -> Type where
    Done : Cover Done Done
    Keep : Cover th ph -> (0 x : a) -> Cover (Keep th x) (Keep ph x)
    DropL : Cover th ph -> (0 x : a) -> Cover (Drop th x) (Keep ph x)
    DropR : Cover th ph -> (0 x : a) -> Cover (Keep th x) (Drop ph x)

  export
  coverDec : (th : Thinning {a} sx1 sy) -> (ph : Thinning sx2 sy) -> Dec (Cover th ph)
  coverDec Done Done = Yes Done
  coverDec (Keep th x) (Keep ph x) with (coverDec th ph)
    _ | Yes p = Yes (Keep p x)
    _ | No np = No (\ (Keep p x) => void (np p))
  coverDec (Keep th x) (Drop ph x) with (coverDec th ph)
    _ | Yes p = Yes (DropR p x)
    _ | No np = No (\ (DropR p x) => void (np p))
  coverDec (Drop th x) (Keep ph x) with (coverDec th ph)
    _ | Yes p = Yes (DropL p x)
    _ | No np = No (\ (DropL p x) => void (np p))
  coverDec (Drop th x) (Drop ph x) = No (\case p impossible)

namespace Join

  public export
  record Join
    {a : Type} {sx1, sx2, sy : SnocList a}
    (th : Thinning sx1 sy)
    (ph : Thinning sx2 sy) where
    constructor MkJoin
    {union : SnocList a}
    {left   : Thinning sx1 union}
    middle : Thinning union sy
    {right  : Thinning sx2 union}
    cover  : Cover left right

  export
  join : {sy : _} -> (th : Thinning sx1 sy) -> (ph : Thinning sx2 sy) -> Join th ph
  join Done Done = MkJoin Done Done
  join (Keep th x) (Keep ph x) =
    let (MkJoin middle cover) = join th ph in
    MkJoin (Keep middle x) (Keep cover x)
  join (Keep th x) (Drop ph x) =
    let (MkJoin middle cover) = join th ph in
    MkJoin (Keep middle x) (DropR cover x)
  join (Drop th x) (Keep ph x) =
    let (MkJoin middle cover) = join th ph in
    MkJoin (Keep middle x) (DropL cover x)
  join (Drop th x) (Drop ph x) =
    let (MkJoin middle cover) = join th ph in
    MkJoin (Drop middle x) cover

namespace Pair

  public export
  data Relevant : (t, p : SnocList a -> Type) -> (sx : SnocList a) -> Type where
    MkRelevant : {sx1, sx2 : _} ->
                 {th : Thinning sx1 sx} -> {ph : Thinning sx2 sx} ->
                 t sx1 -> Cover th ph -> p sx2 -> Relevant t p sx

none : {sx : SnocList a} -> Thinning [<] sx
none {sx = [<]} = Done
none {sx = (sx :< x)} = Drop none x

ones : {sx : SnocList a} -> Thinning sx sx
ones {sx = [<]} = Done
ones {sx = (sx :< x)} = Keep ones x

Scoped : Type -> Type
Scoped a = a -> SnocList a -> Type

data Ty = TyBase | TyArr Ty Ty

Uninhabited (TyBase === TyArr s t) where uninhabited Refl impossible
Uninhabited (TyArr s t === TyBase) where uninhabited Refl impossible

Biinjective TyArr where
  biinjective Refl = (Refl, Refl)

DecEq Ty where
  decEq TyBase TyBase = Yes Refl
  decEq TyBase (TyArr _ _) = No absurd
  decEq (TyArr _ _) TyBase = No absurd
  decEq (TyArr s t) (TyArr a b) = decEqCong2 (decEq s a) (decEq t b)

namespace DeBruijn

  public export
  data Var : Scoped a where
    Here : Var x (sx :< x)
    There : Var v sx -> Var v (sx :< x)

  export
  showVar : All (const String) g -> Var s g -> String
  showVar (_ :< n) Here = n
  showVar (ns :< _) (There v) = showVar ns v

  namespace Var
    export
    thin : Var s g -> Thinning g g' -> Var s g'
    thin v (Drop th x) = There (thin v th)
    thin Here (Keep th x) = Here
    thin (There v) (Keep th x) = There (thin v th)

  export
  Theres : Var s g -> {g' : SnocList a} -> Var s (g <+> g')
  Theres v {g' = [<]} = v
  Theres v {g' = (sx :< x)} = There (Theres v)

  public export
  data Tm : Scoped Ty where
    V : Var s g -> Tm s g
    A : {s : Ty} -> Tm (s `TyArr` t) g -> Tm s g -> Tm t g
    L : {s : Ty} -> Tm t (g :< s) -> Tm (s `TyArr` t) g

  parenthesise : Bool -> String -> String
  parenthesise True str = "(\{str})"
  parenthesise False str = str

  showTerm : Stream String -> All (const String) g -> Prec -> Tm s g -> String
  showTerm gen ns p (V v) = showVar ns v
  showTerm gen ns p (A f t)
    = parenthesise (p >= App)
    $ unwords [ showTerm gen ns Dollar f
              , showTerm gen ns App t
              ]
  showTerm gen ns p (L b)
    = let n = head gen; gen = tail gen in
    parenthesise (p >= Dollar)
    $ unwords [ "\\", "\{n}."
              , showTerm gen (ns :< n) Open b
              ]

  export
  Show (Tm s [<]) where
    show = showTerm gen [<] Open where

      smash1 : Stream (List1 a) -> Stream a
      smash : a -> List a -> Stream (List1 a) -> Stream a

      smash1 ((a ::: as) :: ass) = smash a as ass

      smash a [] ass = a :: smash1 ass
      smash a (b :: as) ass = a :: smash b as ass

      gen : Stream String
      gen = let letters = 'a' ::: unpack "bcdefghijklmnopqrstuvwxyz" in
            smash1
              $ map (\ str => map (`strCons` str) letters)
              $ "" :: map show nats

  namespace Tm
    export
    thin : Tm s g -> Thinning g g' -> Tm s g'
    thin (V v) th = V (thin v th)
    thin (A f t) th = A (thin f th) (thin t th)
    thin (L b) th = L (thin b (Keep th _))

  export
  CONST : Tm (TyArr TyBase $ TyArr TyBase TyBase) [<]
  CONST = L (L (V (There Here)))

  export
  ID : Tm (TyArr TyBase TyBase) [<]
  ID = L (V Here)

  export
  SKIP : Tm (TyArr TyBase $ TyArr TyBase TyBase) [<]
  SKIP = L (L (V Here))

  export
  CONSTS : Tm (TyArr TyBase $ TyArr TyBase TyBase) [<]
  CONSTS = A (A (A (L $ L $ L $ thin CONST none) CONST) CONST) CONST


namespace CoDeBruijn

  %hide DeBruijn.Var
  %hide DeBruijn.Here
  %hide DeBruijn.Tm
  %hide DeBruijn.V
  %hide DeBruijn.A
  %hide DeBruijn.L

  public export
  data Var : Scoped a where
    Here : Var x [<x]

  export
  DecEq (Var x xs) where
    decEq Here Here = Yes Refl

  public export
  data Binding : (t : SnocList a -> Type) -> Scoped a where
    ||| Constant
    K : t g -> Binding t s g
    ||| Relevant
    R : (0 s : a) -> t (g :< s) -> Binding t s g

  export Injective (K {t, s, g}) where injective Refl = Refl
  export Injective (R {t, g} s) where injective Refl = Refl

  export Uninhabited (K {t, s, g} l === R s r) where uninhabited Refl impossible
  export Uninhabited (R {t, g} s l === K r) where uninhabited Refl impossible

  export
  ({0 sx : SnocList a} -> DecEq (t sx)) => DecEq (Binding t x sx) where
    decEq (K t) (K u) = decEqCong (decEq t u)
    decEq (K _) (R _ _) = No absurd
    decEq (R _ _) (K _) = No absurd
    decEq (R x t) (R x u) = decEqCong (decEq t u)

  public export
  data Tm : Scoped Ty where
    V : Var s g -> Tm s g
    A : {s : Ty} -> Relevant (Tm (s `TyArr` t)) (Tm s) g -> Tm t g
    L : {s : Ty} -> Binding (Tm t) s g -> Tm (s `TyArr` t) g

  public export
  appDomain : {s : _} -> Tm s g -> Ty
  appDomain (A {s = dom} _) = dom
  appDomain _ = s

  export Injective (V {s, g}) where injective Refl = Refl
  export {s : Ty} -> Injective (A {s, t, g}) where injective Refl = Refl
  export {s : Ty} -> Injective (L {s, t, g}) where injective Refl = Refl

  export Uninhabited (V v === A {s, t, g} ft) where uninhabited Refl impossible
  export Uninhabited (A {s, t, g} ft === V v) where uninhabited Refl impossible
  export Uninhabited (V v === L {s, t, g} ft) where uninhabited Refl impossible
  export Uninhabited (L {s, t, g} ft === V v) where uninhabited Refl impossible

  export Uninhabited (L {s, t, g} b === A ft) where uninhabited Refl impossible
  export Uninhabited (A ft === L {s, t, g} b) where uninhabited Refl impossible

  export
  DecEq (Tm s g) where
    decEq (V v) (V w) = decEqCong (decEq v w)
    decEq (V _) (A _) = No absurd
    decEq (A _) (V _) = No absurd
    decEq (V _) (L _) = No absurd
    decEq (L _) (V _) = No absurd
    decEq (A {s = s@_} p) (A {s = s'} q) with (decEq s s')
      _ | Yes Refl = decEqCong ?azrpjgzj
      _ | No neq = No (neq . cong appDomain)
    decEq (A _) (L _) = No absurd
    decEq (L _) (A _) = No absurd
    decEq (L b) (L c) = decEqCong (decEq b c)


%unhide DeBruijn.Var
%unhide DeBruijn.Here
%unhide DeBruijn.Tm
%unhide DeBruijn.V
%unhide DeBruijn.A
%unhide DeBruijn.L

namespace Diamond

  public export
  record Diamond {a : Type} (t : SnocList a -> Type) (sx : SnocList a) where
    constructor MkDiamond
    {support : SnocList a}
    selection : Thinning {a} support sx
    selected  : t support

  export
  thin : Diamond t sx -> Thinning sx sy -> Diamond t sy
  thin (MkDiamond th tm) ph = MkDiamond (th <.> ph) tm

  export
  Drop : Diamond t sx -> (0 x : a) -> Diamond {a} t (sx :< x)
  Drop (MkDiamond sel t) x = MkDiamond (Drop sel x) t

  export
  (<$>) : (forall sx. t sx -> u sx) -> Diamond t sx -> Diamond u sx
  f <$> MkDiamond sel t = MkDiamond sel (f t)

  export
  bind : Diamond (CoDeBruijn.Tm t) (g :< s) -> Diamond (Binding (CoDeBruijn.Tm t) s) g
  bind (MkDiamond (Drop sel x) b) = MkDiamond sel (K b)
  bind (MkDiamond (Keep sel x) b) = MkDiamond sel (R x b)

  export
  relevant : {g : _} -> Diamond t g -> Diamond p g -> Diamond (Relevant t p) g
  relevant (MkDiamond th t) (MkDiamond ph p)
    = let (MkJoin middle cover) = join th ph in
      MkDiamond middle (MkRelevant t cover p)

namespace Var

  export
  coDeBruijn : {g : _} -> DeBruijn.Var s g -> Diamond (CoDeBruijn.Var s) g
  coDeBruijn Here = MkDiamond (Keep none _) Here
  coDeBruijn (There v) = Drop (coDeBruijn v) _

  export
  deBruijn : CoDeBruijn.Var s g -> DeBruijn.Var s g
  deBruijn Here = Here

namespace Tm

  export
  coDeBruijn : {g : _} -> DeBruijn.Tm s g -> Diamond (CoDeBruijn.Tm s) g
  coDeBruijn (V v) = V <$> coDeBruijn v
  coDeBruijn (A f t) = A <$> relevant (coDeBruijn f) (coDeBruijn t)
  coDeBruijn (L b) = L <$> bind (coDeBruijn b)

  export
  deBruijn : CoDeBruijn.Tm s g -> Thinning g g' -> DeBruijn.Tm s g'
  deBruijn (V v) th = V (thin (deBruijn v) th)
  deBruijn (A (MkRelevant {th = left} {ph = right} f _ t)) th
    = A (deBruijn f (left <.> th)) (deBruijn t (right <.> th))
  deBruijn (L (K b)) th = L (deBruijn b (Drop th _))
  deBruijn (L (R s b)) th = L (deBruijn b (Keep th s))

namespace CoDeBruijn

  export
  coDeBruijn : DeBruijn.Tm s [<] -> CoDeBruijn.Tm s [<]
  coDeBruijn t = let (MkDiamond Done tm) = coDeBruijn t in tm

  export
  CONST : CoDeBruijn.Tm (TyArr TyBase $ TyArr TyBase TyBase) [<]
  CONST = coDeBruijn DeBruijn.CONST

  export
  SKIP : CoDeBruijn.Tm (TyArr TyBase $ TyArr TyBase TyBase) [<]
  SKIP = coDeBruijn DeBruijn.SKIP

  export
  ID : CoDeBruijn.Tm (TyArr TyBase TyBase) [<]
  ID = coDeBruijn DeBruijn.ID

  export
  CONSTS : CoDeBruijn.Tm (TyArr TyBase $ TyArr TyBase TyBase) [<]
  CONSTS = coDeBruijn DeBruijn.CONSTS

namespace Tm

  ||| abstract here (provided things match up)
  abstractH : {g, g', ctx, s, t : _} ->
              DeBruijn.Var s (g <+> g') -> Diamond (CoDeBruijn.Tm s) g ->
              Diamond (CoDeBruijn.Tm t) (g <+> ctx) ->
              Maybe (Diamond (CoDeBruijn.Tm t) ((g <+> g') <+> ctx))
  abstractH v se@(MkDiamond {support = sx@_} th se'@_) tm@(MkDiamond {support = sy} ph tm')
    with (decEq s t)
    _ | No p = Nothing
    _ | Yes Refl with (decEq sx sy)
      _ | No p = Nothing
      _ | Yes Refl with (decEq se' tm')
        _ | Yes Refl = pure (coDeBruijn (V (Theres v)))
        _ | No p = Nothing

{-
  abstract : {g, s, t : _} -> Diamond (CoDeBruijn.Tm s) g ->
             CoDeBruijn.Tm t g -> Diamond (CoDeBruijn.Tm t) g
  abstract se@(MkDiamond {support = ge} th se') tm
    = case bind (abstractD {g' = []} se (MkDiamond ones tm)) of
       (MkDiamond _ (K _)) => MkDiamond ones tm
       (MkDiamond {support = ga} ph (R abs)) =>
         let (MkJoin middle cover) = join ph th in
         MkDiamond middle (A (MkRelevant (L (R abs)) cover se'))
-}

  first : {xs : SnocList a} ->
          ({x : a} -> DeBruijn.Var x (ys <+> xs) -> p x -> Maybe b) ->
          All p xs -> Maybe b
  first p [<] = Nothing
  first p (xs :< x) = p Here x <|> first (p . There) xs

  export
  abstractR : {g, g', ctx, t : _} ->
              All (\ s => Diamond (CoDeBruijn.Tm s) g) g' ->
              Diamond (CoDeBruijn.Tm t) (g <+> ctx) ->
              Diamond (CoDeBruijn.Tm t) ((g <+> g') <+> ctx)
  abstractR ses tm = case first (\ v, se => abstractH v se tm) ses of
    Just tm => tm
    Nothing => case tm of
      (MkDiamond th (A (MkRelevant {th = left} {ph = right} f cover t))) =>
        let f = assert_total $ abstractR ses (MkDiamond (left <.> th) f) in
        let t = assert_total $ abstractR ses (MkDiamond (right <.> th) t) in
        let ft = A <$> relevant f t in
        ft
      (MkDiamond th (L (K b))) =>
        (L . K) <$> abstractR ses (MkDiamond th b)
      (MkDiamond th (L (R x b))) =>
        L <$> bind (abstractR {ctx = ctx :< x} ses (MkDiamond (Keep th x) b))
      _ => thin tm (Drops ones g' <+> ones)

  export
  CSE : DeBruijn.Tm (TyArr TyBase $ TyArr TyBase TyBase) [<]
  CSE =
    let tm = abstractR {ctx = [<]} [<MkDiamond Done CONST] (MkDiamond Done CONSTS) in
    let MkDiamond th f = L <$> bind tm in
    A (deBruijn f th) CONST

main : IO ()
main = do
  putStrLn "CONST  : \{show $ DeBruijn.CONST}"
  putStrLn "CONSTS : \{show $ DeBruijn.CONSTS}"
  putStrLn "CSE    : \{show $ CSE}"

module Data.Order.Extended

import Data.Order

%default total

public export
data Extended a = MInf | PInf | Lift a

namespace LT

  public export
  data ExtendedLT : (a -> a -> Type) -> (Extended a -> Extended a -> Type) where
    MInfPInf : ExtendedLT lt MInf PInf
    MInfLift : ExtendedLT lt MInf (Lift v)
    LiftLift : {0 v, w : a} -> lt v w -> ExtendedLT lt (Lift v) (Lift w)
    LiftPInf : ExtendedLT lt (Lift v) PInf

  export
  LiftInversion : ExtendedLT lt (Lift x) (Lift y) -> lt x y
  LiftInversion (LiftLift p) = p

  export
  trans : (tr : {x, y, z : a} -> lt x y -> lt y z -> lt x z) ->
          {x, y, z : Extended a} -> ExtendedLT lt x y -> ExtendedLT lt y z -> ExtendedLT lt x z
  trans tr MInfLift (LiftLift q) = MInfLift
  trans tr MInfLift LiftPInf = MInfPInf
  trans tr (LiftLift p) (LiftLift q) = LiftLift (tr p q)
  trans tr (LiftLift p) LiftPInf = LiftPInf

public export
ExtendedGT : (a -> a -> Type) -> (Extended a -> Extended a -> Type)
ExtendedGT gt = flip (ExtendedLT (flip gt))

export Uninhabited (ExtendedLT lt MInf MInf) where uninhabited p impossible
export Uninhabited (ExtendedLT lt (Lift x) MInf) where uninhabited p impossible
export Uninhabited (ExtendedLT lt PInf MInf) where uninhabited p impossible
export Uninhabited (ExtendedLT lt PInf (Lift y)) where uninhabited p impossible
export Uninhabited (ExtendedLT lt PInf PInf) where uninhabited p impossible

namespace EQ

  public export
  data ExtendedEQ : (a -> a -> Type) -> (Extended a -> Extended a -> Type) where
    MInfMInf : ExtendedEQ eq MInf MInf
    LiftLift : {0 v, w : a} -> eq v w -> ExtendedEQ eq (Lift v) (Lift w)
    PInfPInf : ExtendedEQ eq PInf PInf

  export
  LiftInversion : ExtendedEQ eq (Lift x) (Lift y) -> eq x y
  LiftInversion (LiftLift p) = p

export Uninhabited (ExtendedEQ lt MInf (Lift y)) where uninhabited p impossible
export Uninhabited (ExtendedEQ lt MInf PInf) where uninhabited p impossible
export Uninhabited (ExtendedEQ lt (Lift x) MInf) where uninhabited p impossible
export Uninhabited (ExtendedEQ lt (Lift x) PInf) where uninhabited p impossible
export Uninhabited (ExtendedEQ lt PInf (Lift y)) where uninhabited p impossible
export Uninhabited (ExtendedEQ lt PInf MInf) where uninhabited p impossible


export
trichotomous : ((x, y : a) -> Trichotomous lt eq gt x y) ->
               ((x, y : Extended a) -> Trichotomous (ExtendedLT lt) (ExtendedEQ eq) (ExtendedGT gt) x y)
trichotomous tri MInf     MInf     = MkEQ absurd   MInfMInf absurd
trichotomous tri MInf     (Lift y) = MkLT MInfLift absurd   absurd
trichotomous tri MInf     PInf     = MkLT MInfPInf absurd   absurd
trichotomous tri (Lift x) MInf     = MkGT absurd   absurd   MInfLift
trichotomous tri (Lift x) PInf     = MkLT LiftPInf absurd   absurd
trichotomous tri PInf     MInf     = MkGT absurd   absurd   MInfPInf
trichotomous tri PInf     (Lift y) = MkGT absurd   absurd   LiftPInf
trichotomous tri PInf     PInf     = MkEQ absurd   PInfPInf absurd
trichotomous tri (Lift x) (Lift y) with (tri x y)
  trichotomous tri (Lift x) (Lift y) | MkLT p q r
    = MkLT (LiftLift p)           (q . EQ.LiftInversion) (r . LT.LiftInversion)
  trichotomous tri (Lift x) (Lift y) | MkEQ p q r
    = MkEQ (p . LT.LiftInversion) (LiftLift q)           (r . LT.LiftInversion)
  trichotomous tri (Lift x) (Lift y) | MkGT p q r
    = MkGT (p . LT.LiftInversion) (q . EQ.LiftInversion) (LiftLift r)

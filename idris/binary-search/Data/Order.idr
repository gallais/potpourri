module Data.Order

%default total

public export
data Trichotomous : (lt, eq, gt : a -> a -> Type) -> (a -> a -> Type) where
  MkLT : {0 lt, eq, gt : a -> a -> Type} ->
         lt v w       -> Not (eq v w) -> Not (gt v w) -> Trichotomous lt eq gt v w
  MkEQ : {0 lt, eq, gt : a -> a -> Type} ->
         Not (lt v w) -> eq v w       -> Not (gt v w) -> Trichotomous lt eq gt v w
  MkGT : {0 lt, eq, gt : a -> a -> Type} ->
         Not (lt v w) -> Not (eq v w) -> gt v w       -> Trichotomous lt eq gt v w

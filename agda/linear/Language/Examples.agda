module linear.Language.Examples where

open import Data.Fin
open import linear.Type
open import linear.Language

identity : Check 0
identity = `lam (`neu (`var zero))

swap : Check 0
swap = `lam `let (`v ,, `v) ∷= `var zero
            `in `prd (`neu `var (suc zero)) (`neu `var zero)

illTyped : Check 0
illTyped = `let (`v ,, `v) ∷= `cut (`inl (`lam (`neu (`var zero)))) ((κ 0 ─o κ 0) ⊕ κ 1)
           `in `prd (`neu (`var zero)) (`neu (`var (suc zero)))

diag : Check 0
diag = `lam (`prd (`neu (`var zero)) (`neu (`var zero)))

omega : Infer 0
omega =  let delta = `lam (`neu (`app (`var zero) (`neu (`var zero))))
         in `app (`cut delta (κ 0)) delta

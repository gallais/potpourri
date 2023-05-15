{-# OPTIONS --allow-exec #-}

module Main where

open import Data.Bool.Base using (true; false)
open import Data.List.Base using (_∷_; [])
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Maybe.Base using (nothing; just)
open import Data.Product.Base using (proj₁; proj₂)
open import Data.String.Base using (String)
open import Data.Unit.Base using (⊤)

open import Function.Base using (_∘′_; _$_; case_of_)

open import Reflection.TCM using (TC; unify)
import Reflection.TCM.Syntax as TCM
open import Reflection.AST.Literal using (string)
open import Reflection.AST.Term using (Term; lit)
open import Reflection.External using (runCmdTC; cmdSpec)


macro

  -- this is a special copy of `runCmd` but turns out we cannot
  -- specialise a macro by partially applying it
  getTemplate : String → Term → TC ⊤
  getTemplate fp hole
    = let open TCM in
      runCmdTC (cmdSpec "cat" (fp ∷ []) "")
      >>= unify hole ∘′ lit ∘′ string

test : String
test = getTemplate "patates.tmp"

open import TMustache.Scoped

{-
values : ⟦ _ ⟧s
values = "vers" ≔ (("jour" ≔ "lundi" ∷ [])
                ∷ ("jour" ≔ "mardi" ∷ [])
                ∷ ("jour" ≔ "mercredi" ∷ [])
                ∷ [])
  ∷ []
-}

values : ⟦ _ ⟧s
values
  = "vers" ≔ (("jour" ≔ "lundi" ∷ "aussi" ≔ false ∷ [])
           ∷ ("jour" ≔ "mardi" ∷ "aussi" ≔ false ∷ [])
           ∷ ("jour" ≔ "mercredi" ∷ "aussi" ≔ true ∷ [])
           ∷ [])
  ∷ []

open import IO
open import System.Exit

main : Main
main = run $ do
  putStrLn $ asTemplate test values

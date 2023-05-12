{-# OPTIONS --allow-exec #-}

module Main where

open import Data.Bool.Base using (true; false)
open import Data.List.Base using (_∷_; [])
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Product.Base using (proj₁; proj₂)
open import Data.String.Base using (String)
open import Data.Unit.Base using (⊤)

open import Function.Base using (_∘′_; _$_)

open import Reflection.TCM using (TC; unify)
open import Reflection.TCM.Syntax using (_>>=_)
open import Reflection.AST.Literal using (string)
open import Reflection.AST.Term using (Term; lit)
open import Reflection.External using (runCmdTC; cmdSpec)


macro

  -- this is a special copy of `runCmd` but turns out we cannot
  -- specialise a macro by partially applying it
  getTemplate : String → Term → TC ⊤
  getTemplate fp hole
    = runCmdTC (cmdSpec "cat" (fp ∷ []) "")
      >>= unify hole ∘′ lit ∘′ string

test : String
test = getTemplate "patates.tmp"

open import TMustache.Scoped

open import Data.Maybe using (to-witness-T)

{-
template : Mustache _ _
template = proj₂ (to-witness-T (scope test) _)
-}

values : ⟦ _ ⟧sc
values
  = "vers" ≔ ("jour" ≔ "lundi" ∷ "aussi" ≔ false ∷ []
           ∷ ("jour" ≔ "mardi" ∷ "aussi" ≔ false ∷ [])
           ∷ ("jour" ≔ "mercredi" ∷ "aussi" ≔ true ∷ [])
           ∷ [])
  ∷ []

open import IO

main : Main
main = run $ do
  putStrLn $ instMustache {!!} values

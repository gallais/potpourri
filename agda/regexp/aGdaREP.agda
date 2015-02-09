module regexp.aGdaREP where

open import Level
open import Coinduction
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.Char   as Chr
open import Data.String as Str
open import Data.List   as List
open import Data.Maybe  as Maybe

open import Function
open import lib.Nullary

import regexp.Search
module S = regexp.Search Char Chr._≟_
open S

lit : (str : String) → RegExp
lit = List.foldr (_∙_ ∘ RE.[_]) ε ∘ Str.toList

grep : RegExp → String → Maybe String
grep e str = dec (substring e (Str.toList str)) (just ∘′ grab) (const nothing)
  where
    grab : Substring e (Str.toList str) → String
    grab (ss , ts , us , _ , _) =
        Str.fromList $ ss List.++ Str.toList "\x1B[1m \x1B[31m"
                          List.++ ts
                          List.++ Str.toList "\x1B[0m"
                          List.++ us
                            

coloUr : RegExp
coloUr = lit "colo" ∙ (lit "u" ⁇) ∙ lit "r"

open import IO           as IO
import IO.Primitive      as Prim
open import Data.Colist  as Colist

breakOn : {A : Set} (P? : A → Bool) (xs : List A) → List (List A)
breakOn {A} P? = uncurry _∷_ ∘ foldr step ([] , [])
  where
    step : A → (List A × List (List A)) → (List A × List (List A))
    step a (xs , xss) = if (P? a) then [] , xs ∷ xss else a ∷ xs , xss

lines : String → List String
lines = List.map Str.fromList ∘ breakOn isNewLine ∘ Str.toList
  where
    isNewLine : Char → Bool
    isNewLine y = dec (y Chr.≟ '\n') (const true) (const false)

module myPrimIO where

  {-# IMPORT System.Environment #-}

  postulate
    getArgs     : Prim.IO (List String)

  {-# COMPILED getArgs        System.Environment.getArgs               #-}

getArgs : IO (List String)
getArgs = lift myPrimIO.getArgs

main : _
main =
  IO.run $
  ♯ getArgs >>= λ args →
  ♯ (case args of λ
     { []       → return (lift tt)
     ; (hd ∷ _) →
       ♯ IO.readFiniteFile hd >>= λ content →
       ♯ (IO.mapM′ (maybe putStrLn (return tt))
         $ Colist.fromList
         $ List.map (grep coloUr)
         $ lines content)
  })
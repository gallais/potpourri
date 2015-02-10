module regexp.aGdaREP where

open import Level
open import Coinduction
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.Sum
open import Data.Char   as Chr
open import Data.String as Str
open import Data.List   as List
open import Data.Maybe  as Maybe

open import Function
open import Relation.Nullary
open import lib.Nullary

import regexp.Search
module S = regexp.Search Char Chr._≟_
open S

{-
    ∅   : RegExp
    ε   : RegExp
    ─   : RegExp
    [_] : (a : Alphabet) → RegExp
    _⋆  : (e : RegExp) → RegExp
-}

data Error : Set where
  TooManyClosingParentheses   : Error
  NotEnoughClosingParentheses : Error

parse : List (RegExp → RegExp) → List Char → RegExp ⊎ Error
parse []           _                = inj₂ TooManyClosingParentheses
parse (e ∷ [])     []               = inj₁ $ e ε
parse _            []               = inj₂ NotEnoughClosingParentheses
parse (e ∷ es)     ('\\' ∷ x ∷ xs)  = parse ((λ f → e RE.[ x ] `∙ f) ∷ es) xs
parse es           ('(' ∷ xs)       = parse (id ∷ es) xs
parse (e ∷ es)     ('|' ∷ xs)       = parse ((λ f → e ε ∣ f) ∷ es) xs
parse (e ∷ [])     (')' ∷ xs)       = inj₂ TooManyClosingParentheses
parse (e ∷ f ∷ es) (')' ∷ '?' ∷ xs) = parse ((λ g → f (e ε ⁇ `∙ g)) ∷ es) xs
parse (e ∷ f ∷ es) (')' ∷ '*' ∷ xs) = parse ((λ g → f (e ε `⋆ `∙ g)) ∷ es) xs
parse (e ∷ f ∷ es) (')' ∷ xs)       = parse ((λ g → f (e ε `∙ g)) ∷ es) xs
parse (e ∷ es)     ('.' ∷ '?' ∷ xs) = parse ((λ f → e (─ ⁇ `∙ f)) ∷ es) xs
parse (e ∷ es)     ('.' ∷ '*' ∷ xs) = parse ((λ f → e (─ `⋆ `∙ f)) ∷ es) xs
parse (e ∷ es)     ('.' ∷ xs)       = parse ((λ f → e (─ `∙ f)) ∷ es) xs
parse (e ∷ es)     (a   ∷ '?' ∷ xs) = parse ((λ f → e (RE.[ a ] ⁇ `∙ f)) ∷ es) xs
parse (e ∷ es)     (a   ∷ '*' ∷ xs) = parse ((λ f → e (RE.[ a ] `⋆ `∙ f)) ∷ es) xs
parse (e ∷ es)     (a   ∷ xs)       = parse ((λ f → e (RE.[ a ] `∙ f)) ∷ es) xs

parseRegExp : String → RegExp ⊎ Error
parseRegExp = parse (id ∷ []) ∘ Str.toList

select : RegExp → String → Maybe String
select e str = dec (substring e (Str.toList str)) (just ∘′ grab) (const nothing)
  where
    grab : Substring e (Str.toList str) → String
    grab (ss , ts , us , _ , _) =
        Str.fromList $ ss List.++ Str.toList "\x1B[1m\x1B[31m"
                          List.++ ts
                          List.++ Str.toList "\x1B[0m"
                          List.++ us

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

usage : IO (Lift ⊤)
usage = ♯ IO.putStrLn "Usage: aGdaREP regexp filename" >> ♯ return (lift tt)

FilePath : Set
FilePath = String

grep : RegExp → FilePath → IO (Lift ⊤)
grep reg fp = 
  ♯ IO.readFiniteFile fp >>= λ content →
  ♯ (IO.mapM′ (maybe putStrLn (return tt))
    $ Colist.fromList
    $ List.map (select reg)
    $ lines content)

main : _
main =
  IO.run $
  ♯ getArgs >>= λ args →
  ♯ (case args of λ
     { (reg ∷ fp ∷ _) → [ flip grep fp , const $ return (lift tt) ]′ (parseRegExp reg)
     ; _              → usage
     })
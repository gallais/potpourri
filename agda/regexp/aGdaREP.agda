module regexp.aGdaREP where

open import Data.Product
open import Data.Char   as Chr
open import Data.String as Str
open import Data.List   as List

open import Function
open import lib.Nullary

import regexp.Search
module S = regexp.Search Char Chr._≟_
open S

lit : (str : String) → RegExp
lit = List.foldr (_∙_ ∘ RE.[_]) ε ∘ Str.toList

grep : RegExp → List String → List String
grep e = foldr cons []
  where
    grab : {str : List Char} → Substring e str → String
    grab (ss , ts , us , _ , _) =
        Str.fromList $ ss List.++ Str.toList "\x1B[1m \x1B[31m"
                          List.++ ts
                          List.++ Str.toList "\x1B[0m"
                          List.++ us
                            

    cons : String → List String → List String
    cons str = dec (substring e (Str.toList str)) (_∷_ ∘ grab) (const id)

coloUr : RegExp
coloUr = lit "colo" ∙ (lit "u" ⁇) ∙ lit "r"

open import IO as IO
open import Data.Colist as Colist

main : _
main =
  IO.run $ IO.mapM putStrLn $ Colist.fromList
  $ grep coloUr
  $ "green is a nice colour, isn't it?"
  ∷ "I prefer orange myself"
  ∷ "Orange the fruit or orange the color?"
  ∷ []
    

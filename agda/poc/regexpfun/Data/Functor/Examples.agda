module Data.Functor.Examples where

open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.List   as List
open import Function
open import lib.Nullary
open import Relation.Binary.PropositionalEquality

open import Data.Functor

ListDesc : Desc
ListDesc = `K ⊤ `+ `L `* `X

TreeDesc : Desc
TreeDesc = `L `+ `X `* `X

module ValueConstrainedExamples where

  open import Data.Char   as Chr
  open import lib.Char    as Char
  open import RegExp.Search Char Char._≤_ Chr._≟_ Char._≤?_
  open ValueConstrained Char Char._≤_ Chr._≟_ Char._≤?_

  EvenLength : RegExp
  EvenLength = (─ ∙ ─) ⋆

  OddLength : RegExp
  OddLength = ─ ∙ EvenLength

  EvenList : Set
  EvenList = μ ListDesc EvenLength

  infixr 5 _∷₁_ _∷₂_
  _∷₁_ : Char → `μ ListDesc OddLength EvenLength → `μ ListDesc EvenLength EvenLength
  c ∷₁ cs = ⟨ inj₂ (_ , (c , refl) , cs) ⟩
  _∷₂_ :  Char → `μ ListDesc EvenLength EvenLength → `μ ListDesc OddLength EvenLength
  c ∷₂ cs = ⟨ inj₂ (_ , (c , refl) , cs) ⟩

  `[] : `μ ListDesc EvenLength EvenLength
  `[] = ⟨ inj₁ (tt , refl) ⟩

  someList : EvenList
  someList =
      EvenLength
    , tactics hasEmpty EvenLength
    , 'h' ∷₁ 'e' ∷₂ 'l' ∷₁ 'l' ∷₂ 'o' ∷₁ ' ' ∷₂
      'w' ∷₁ 'o' ∷₂ 'r' ∷₁ 'l' ∷₂ 'd' ∷₁ '!' ∷₂ `[]

  EvenTree : Set
  EvenTree = μ TreeDesc EvenLength

  leaf₁ : Char → `μ TreeDesc EvenLength OddLength
  leaf₁ c = ⟨ inj₁ (c , refl) ⟩

  leaf₂ : Char → `μ TreeDesc OddLength EvenLength
  leaf₂ c = ⟨ inj₁ (c , refl) ⟩

  node : {a b c : RegExp} → `μ TreeDesc a b → `μ TreeDesc b c → `μ TreeDesc a c
  node {b = b} l r = ⟨ inj₂ (b , l , r) ⟩

  someTree : EvenTree
  someTree =
      EvenLength
    , tactics hasEmpty EvenLength
    , node (node (node (leaf₁                   'h')
                       (node (leaf₂             'e')
                             (leaf₁             'l')))
                 (node (leaf₂                   'l')
                       (leaf₁                   'o')))
           (node (node (leaf₂                   ' ')
                       (node (node (leaf₁       'w')
                                   (leaf₂       'o'))
                             (node (node (leaf₁ 'r')
                                         (leaf₂ 'l'))
                                   (leaf₁       'd'))))
                 (leaf₂                         '!'))

module TypeConstrainedExamples where

  open import Data.Fin
  open import Data.Char
  open import Data.String
  open import Data.Vec
  open TypeConstrained 3

  EvenLength : RegExp
  EvenLength = (RE.[ exact zero ∷ [] ] ∙ RE.[ exact (suc zero) ∷ [] ]) ⋆

  OddLength : RegExp
  OddLength = RE.[ exact (suc zero) ∷ [] ] ∙ EvenLength

  ρ = flip lookup (Char ∷ String ∷ ⊤ ∷ [])

  EvenList : Set
  EvenList = μ ListDesc ρ EvenLength

  infixr 5 _∷₁_ _∷₂_
  _∷₁_ : Char → `μ ListDesc ρ OddLength EvenLength → `μ ListDesc ρ EvenLength EvenLength
  c ∷₁ cs = ⟨ inj₂ (_ , (zero , c , refl) , cs) ⟩
  _∷₂_ :  String → `μ ListDesc ρ EvenLength EvenLength → `μ ListDesc ρ OddLength EvenLength
  c ∷₂ cs = ⟨ inj₂ (_ , (suc zero , c , refl) , cs) ⟩

  `[] : `μ ListDesc ρ EvenLength EvenLength
  `[] = ⟨ inj₁ (tt , refl) ⟩

  someList : EvenList
  someList =
      EvenLength
    , tactics hasEmpty EvenLength
    , 'h' ∷₁ "e" ∷₂ 'l' ∷₁ "l" ∷₂ 'o' ∷₁ " " ∷₂
      'w' ∷₁ "o" ∷₂ 'r' ∷₁ "l" ∷₂ 'd' ∷₁ "!" ∷₂ `[]
module Section4.Core where

open import Data.Nat
import Data.Integer as ℤ
open import Data.Bool
open import Data.Product
open import Data.List as List
open import Data.Vec as Vec hiding (group)
open import Data.Char as Char
open import Data.String as String
open import Data.String.Extra
open import Function
open import Relation.Binary.PropositionalEquality

import Section2.Core as S2


record Press {ℓ} (Doc : Set ℓ) : Set ℓ where
  infixr 5 _<>_
  field
    _<>_   : Doc → Doc → Doc
    ε      : Doc
    text   : String → Doc
    line   : Doc
    nest   : ℕ → Doc → Doc
    group  : Doc → Doc
    layout : ℕ → Doc → String
    _<+/>_ : Doc → Doc → Doc
    fill   : List Doc → Doc

  foldDoc : (Doc → Doc → Doc) → List Doc → Doc
  foldDoc f []       = ε
  foldDoc f (x ∷ []) = x
  foldDoc f (x ∷ xs) = f x (foldDoc f xs)


  _<+>_ = λ d e → d <> text " " <> e
  spread = foldDoc _<+>_

  _</>_ = λ d e → d <> line <> e
  stack  = foldDoc _</>_

  fillWords = foldDoc _<+/>_ ∘ List.map text ∘ words
    where 

  bracket = λ l d r → group $
            text l
         <> nest 2 (line <> d)
         <> line <> text r

private

  infixr 5 _<>_
  infixr 4 _<|>_
  data Doc : Bool → Set where
    []    : ∀ {b} → Doc b
    _<>_  : ∀ {b c} → Doc b → Doc c → Doc (b ∨ c)
    txt   : ∀ {b} → String → Doc b
    _>>_  : ∀ {b} → ℕ → Doc b → Doc b
    ln    : ∀ {b} → Doc b
    _<|>_ : ∀ {b c} → Doc b → Doc c → Doc true

press : Press (Doc true)
press = record
  { _<>_   = _<>_
  ; ε      = []
  ; text   = txt
  ; line   = ln
  ; nest   = _>>_
  ; group  = group
  ; layout = layout
  ; _<+/>_ = _<+/>_
  ; fill   = fill ∘ Vec.fromList
  } module pressImplementation where

  _<+/>_ : ∀ {b c} → Doc b → Doc c → Doc true
  _<+/>_ {false} d e = d <> ((Doc false ∋ txt " ") <|> (Doc false ∋ ln)) <> e
  _<+/>_ {true}  d e = d <> ((Doc false ∋ txt " ") <|> (Doc false ∋ ln)) <> e

  -- We use the index to short-circuit the flattening
  -- in case we already know that the Doc is sum-free.
  flatten  : ∀ {b} → Doc b → Doc false
  flatten′ : ∀ {b} → Doc b → Doc false

  flatten {false} d = d
  flatten         d = flatten′ d

  flatten′ []        = []
  flatten′ (d <> e)  = flatten d <> flatten e
  flatten′ (txt s)   = txt s
  flatten′ (n >> d)  = flatten d
  flatten′ ln        = txt " "
  flatten′ (d <|> e) = flatten d

  -- Same here
  forget  : ∀ {b} → Doc b → Doc true
  forget′ : ∀ {b} → Doc b → Doc true

  forget {true} d = d
  forget        d = forget′ d

  forget′ []        = []
  forget′ (d <> e)  = forget d <> forget e
  forget′ (txt s)   = txt s
  forget′ (n >> d)  = n >> forget d
  forget′ ln        = ln
  forget′ (d <|> e) = d <|> e

  -- Using Vectors makes termination obvious
  fill : {n : ℕ} → Vec (Doc true) n → Doc true
  fill []           = []
  fill (d ∷ [])     = d
  fill (d ∷ e ∷ ds) =
    let _<+>_ = λ d e → d <> (Doc false ∋ txt " ") <> e
        _</>_ = λ d e → d <> (Doc false ∋ ln) <> e
    in flatten d <+> fill (forget (flatten e) ∷ ds)
       <|> d </> fill (e ∷ ds)

  group : ∀ {b} → Doc b → Doc true
  group d = flatten d <|> d

  -- Using a CPS-transformed version of best makes termination obvious
  best : ∀ {b} → ℕ → Doc b → S2.Doc false
  best w d = go w 0 0 d $ λ _ → S2.[] where

    go : ∀ {b} → ℕ → ℕ → ℕ → Doc b → (ℕ → S2.Doc false) → S2.Doc false
    go w k i []        ds = ds k
    go w k i (d <> e)  ds = go w k i d $ λ k → go w k i e ds
    go w k i (txt s)   ds = s S2.<< ds (k + length (String.toList s))
    go w k i (n >> d)  ds = go w k (i + n) d ds
    go w k i ln        ds = i S2.vv ds i
    go w k i (d <|> e) ds = better w k (go w k i d ds) (go w k i e ds)
      where open S2.pressImplementation

  layout : ℕ → Doc true → String
  layout w d = S2.pressImplementation.layout $ best w d

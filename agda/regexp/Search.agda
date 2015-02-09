open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Data.Empty
open import Data.Bool     hiding (_≟_)
open import Data.Maybe    as Maybe
open import Data.Product  as Product
open import Data.Sum      as Sum
open import Data.List     as List    using (List ; [] ; _∷_)

open import lib.Nullary
open import Function

module regexp.Search
       (Alphabet : Set)
       (_≟_ : (a b : Alphabet) → Dec (a ≡ b))
       where

  import regexp.SmartCons
  module SC = regexp.SmartCons Alphabet _≟_
  open SC public

  ∈∣-invert : {xs : List Alphabet} {e f : RegExp} → xs ∈ e ∣ f → xs ∈ e ⊎ xs ∈ f
  ∈∣-invert (pr ∣₁ f) = inj₁ pr
  ∈∣-invert (e ∣₂ pr) = inj₂ pr

  []∈∙-invert : {e f : RegExp} → [] ∈ e ∙ f → [] ∈ e × [] ∈ f
  []∈∙-invert (_∙_⇚_ {[]}     {[]}     pr₁ pr₂ eq) = pr₁ , pr₂
  []∈∙-invert (_∙_⇚_ {[]}     {y ∷ ys} pr₁ pr₂ ())
  []∈∙-invert (_∙_⇚_ {x ∷ xs} {_}      pr₁ pr₂ ())

  hasEmpty : (e : RegExp) → Dec ([] ∈ e)
  hasEmpty ∅       = no (λ ())
  hasEmpty ε       = yes ε
  hasEmpty ─       = no (λ ())
  hasEmpty [ a ]   = no (λ ())
  hasEmpty (e ∣ f) = dec (hasEmpty e) (yes ∘ flip _∣₁_ f) $ λ ¬∈e →
                     dec (hasEmpty f) (yes ∘ _∣₂_ e)      $ λ ¬∈f →
                     no $ [ ¬∈e , ¬∈f ]′ ∘ ∈∣-invert
  hasEmpty (e ∙ f) = flip (dec (hasEmpty e)) (λ ¬∈e → no $ ¬∈e ∘ proj₁ ∘ []∈∙-invert) $ λ ∈e →
                     flip (dec (hasEmpty f)) (λ ¬∈f → no $ ¬∈f ∘ proj₂ ∘ []∈∙-invert) $ λ ∈f →
                     yes $ ∈e ∙ ∈f ⇚ refl
  hasEmpty (e ⋆)   = yes $ ε ∣₁ (e ∙ e ⋆) ⋆

  infix 4 _⟪_
  _⟪_ : (e : RegExp) (a : Alphabet) → RegExp
  ∅       ⟪ a = ∅
  ε       ⟪ a = ∅
  ─       ⟪ a = ε
  [ b ]   ⟪ a = dec (a ≟ b) (const ε) (const ∅)
  e₁ ∣ e₂ ⟪ a = (e₁ ⟪ a) `∣ (e₂ ⟪ a)
  e₁ ∙ e₂ ⟪ a = dec (hasEmpty e₁)
                (const $ ((e₁ ⟪ a) `∙ e₂) `∣ (e₂ ⟪ a))
                (const $ (e₁ ⟪ a) `∙ e₂)
  e ⋆     ⟪ a = (e ⟪ a) `∙ (e `⋆)

  ⟪-sound : (x : Alphabet) (xs : List Alphabet) (e : RegExp) →
            xs ∈ e ⟪ x → x ∷ xs ∈ e
  ⟪-sound x xs ∅ ()
  ⟪-sound x xs ε ()
  ⟪-sound x .[] ─ ε = ─
  ⟪-sound x xs [ a ] pr with x ≟ a
  ⟪-sound x .[] [ .x ] ε | yes refl = [ x ]
  ⟪-sound x xs [ a ] () | no ¬p
  ⟪-sound x xs (e ∣ f) pr with `∣-sound (e ⟪ x) (f ⟪ x) pr
  ... | pr′ ∣₁ .(f ⟪ x) = ⟪-sound x xs e pr′ ∣₁ f
  ... | .(e ⟪ x) ∣₂ pr′ = e ∣₂ ⟪-sound x xs f pr′
  ⟪-sound x xs (e ∙ f) pr with hasEmpty e
  ... | yes p with `∣-sound ((e ⟪ x) `∙ f) (f ⟪ x) pr
  ⟪-sound x xs (e ∙ f) pr | yes p | ._ ∣₂ pr′ = p ∙ ⟪-sound x xs f pr′ ⇚ refl
  ⟪-sound x xs (e ∙ f) pr | yes p | pr′ ∣₁ .(f ⟪ x) with `∙-sound (e ⟪ x) f pr′
  ⟪-sound x ._ (e ∙ f) pr | yes p | pr′ ∣₁ .(f ⟪ x) | pr′′₁ ∙ pr′′₂ ⇚ refl = ⟪-sound x _ e pr′′₁ ∙ pr′′₂ ⇚ refl
  ⟪-sound x xs (e ∙ f) pr | no ¬p with `∙-sound (e ⟪ x) f pr
  ⟪-sound x ._ (e ∙ f) pr | no ¬p | pr′₁ ∙ pr′₂ ⇚ refl = ⟪-sound x _ e pr′₁ ∙ pr′₂ ⇚ refl
  ⟪-sound x xs (e ⋆) pr with `∙-sound (e ⟪ x) (e `⋆) pr
  ⟪-sound x ._ (e ⋆) pr | pr′₁ ∙ pr′₂ ⇚ refl = (ε ∣₂ (⟪-sound x _ e pr′₁ ∙ `⋆-sound e pr′₂ ⇚ refl)) ⋆

  ⟪-complete : (x : Alphabet) (xs : List Alphabet) (e : RegExp) →
               x ∷ xs ∈ e → xs ∈ e ⟪ x
  ⟪-complete x .[] .─ ─ = ε
  ⟪-complete x .[] .([ x ]) [ .x ] with x ≟ x
  ⟪-complete x .[] .([ x ]) [ .x ] | yes p = ε
  ⟪-complete x .[] .([ x ]) [ .x ] | no ¬p = ⊥-elim (¬p refl)
  ⟪-complete x xs (e ∣ f) (pr ∣₁ .f) = `∣-complete (e ⟪ x) (f ⟪ x) (⟪-complete x xs e pr ∣₁ (f ⟪ x))
  ⟪-complete x xs (e ∣ f) (.e ∣₂ pr) = `∣-complete (e ⟪ x) (f ⟪ x) ((e ⟪ x) ∣₂ ⟪-complete x xs f pr)
  ⟪-complete x xs (e ∙ f) (pr ∙ pr₁ ⇚ x₁) with hasEmpty e
  ⟪-complete x xs (e ∙ f) (_∙_⇚_ {[]} pr₁ pr₂ refl)        | yes p = `∣-complete ((e ⟪ x) `∙ f) (f ⟪ x) (_ ∣₂ ⟪-complete x _ f pr₂)
  ⟪-complete x ._ (e ∙ f) (_∙_⇚_ {.x ∷ ys} pr₁ pr₂ refl)   | yes p = `∣-complete ((e ⟪ x) `∙ f) (f ⟪ x) (`∙-complete (e ⟪ x) f (⟪-complete x _ e pr₁ ∙ pr₂ ⇚ refl) ∣₁ _)
  ⟪-complete x xs (e ∙ f) (_∙_⇚_ {[]}     {zs} pr₁ pr₂ eq) | no ¬p = ⊥-elim (¬p pr₁)
  ⟪-complete x ._ (e ∙ f) (_∙_⇚_ {.x ∷ ys} pr₁ pr₂ refl)   | no ¬p = `∙-complete (e ⟪ x) f (⟪-complete x _ e pr₁ ∙ pr₂ ⇚ refl)
  ⟪-complete x xs ._ (() ∣₁ ._ ⋆)
  ⟪-complete x xs (e ⋆) (.ε ∣₂ _∙_⇚_ {[]} pr₁ pr₂ refl ⋆)      = ⟪-complete x xs (e ⋆) pr₂
  ⟪-complete x ._ (e ⋆) (.ε ∣₂ _∙_⇚_ {.x ∷ ys} pr₁ pr₂ refl ⋆) = `∙-complete (e ⟪ x) (e `⋆) (⟪-complete x _ _ pr₁ ∙ `⋆-complete e pr₂ ⇚ refl)

  Prefix  : (e : RegExp) (xs : List Alphabet) → Set
  Prefix e xs = Σ[ ys ∈ List Alphabet ] Σ[ zs ∈ List Alphabet ]
                xs ≡ ys List.++ zs × ys ∈ e

  ¬Prefix[] : {e : RegExp} (¬[]∈e : ¬ ([] ∈ e)) → ¬ Prefix e []
  ¬Prefix[] ¬[]∈e ([]     , zs , eq , pr) = ¬[]∈e pr
  ¬Prefix[] ¬[]∈e (x ∷ ys , zs , () , pr)

  ¬Prefix∷ : {e : RegExp} {x : Alphabet} {xs : List Alphabet}
             (¬[]∈e : ¬ ([] ∈ e)) (¬∷∈e : ¬ Prefix (e ⟪ x) xs) → ¬ Prefix e (x ∷ xs)
  ¬Prefix∷ ¬[]∈e ¬pr ([]     , zs , eq   , pr) = ¬[]∈e pr
  ¬Prefix∷ ¬[]∈e ¬pr (y ∷ ys , zs , refl , pr) = ¬pr (ys , zs , refl , ⟪-complete y ys _ pr)

  prefix : (e : RegExp) (xs : List Alphabet) → Dec (Prefix e xs)
  prefix e []       = dec (hasEmpty e) (λ []∈e → yes $ [] , [] , refl , []∈e) (no ∘ ¬Prefix[])
  prefix ∅ _        = no (λ { (_ , _ , _ , ()) })
  prefix e (x ∷ xs) = dec (hasEmpty e) (λ []∈e → yes $ [] , x ∷ xs , refl , []∈e) $ λ ¬[]∈e →
                      dec (prefix (e ⟪ x) xs)
                      (λ { (ys , zs , eq , pr) → yes $ x ∷ ys , zs , cong (_∷_ x) eq , ⟪-sound x ys e pr })
                      (no ∘ ¬Prefix∷ ¬[]∈e)

  Substring : (e : RegExp) (xs : List Alphabet) → Set
  Substring e xs = Σ[ ss ∈ List Alphabet ] Σ[ ts ∈ List Alphabet ] Σ[ us ∈ List Alphabet ]
                   xs ≡ ss List.++ ts List.++ us × ts ∈ e

  ¬Substring[] : {e : RegExp} (¬here : ¬ Prefix e []) → ¬ (Substring e [])
  ¬Substring[] ¬here ([]     , ts , us , eq , pr) = ¬here (ts , us , eq , pr)
  ¬Substring[] ¬here (x ∷ ss , ts , us , () , pr)

  ¬Substring∷ : {e : RegExp} {x : Alphabet} {xs : List Alphabet}
                (¬here : ¬ Prefix e (x ∷ xs)) (¬there : ¬ Substring e xs) → ¬ Substring e (x ∷ xs)
  ¬Substring∷ ¬here ¬there ([]     , ts , us , eq   , pr) = ¬here (ts , us , eq , pr)
  ¬Substring∷ ¬here ¬there (x ∷ ss , ts , us , refl , pr) = ¬there (ss , ts , us , refl , pr)

  substring : (e : RegExp) (xs : List Alphabet) → Dec (Substring e xs)
  substring e []       = dec (prefix e []) (λ { (ys , zs , eq , pr) → yes ([] , ys , zs , eq , pr) })
                         (no ∘ ¬Substring[])
  substring e (x ∷ xs) = dec (prefix e (x ∷ xs)) (λ { (ys , zs , eq , pr) → yes ([] , ys , zs , eq , pr) }) $ λ ¬x →
                         dec (substring e xs)
                             (λ { (ss , ts , us , eq , pr) → yes (x ∷ ss , ts , us , cong (_∷_ x) eq , pr) })
                             (no ∘ ¬Substring∷ ¬x)

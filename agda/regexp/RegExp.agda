module RegExp where

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Data.Empty
open import Data.Bool     hiding (_≟_)
open import Data.Maybe    as Maybe
open import Data.Product  as Product

open import lib.Nullary
open import Function

module RegularExp (Alphabet : Set)
       (_≟_ : (a b : Alphabet) → Dec (a ≡ b))
       where

  infixr 5 _∣_ _`∣_
  infixr 6 _∙_ _`∙_
  infix  7 _⋆ _`⋆
  data RegExp : Set where
    ∅   : RegExp
    ε   : RegExp
    ─   : RegExp
    [_] : (a : Alphabet) → RegExp
    _∣_ : (e₁ e₂ : RegExp) → RegExp
    _∙_ : (e₁ e₂ : RegExp) → RegExp
    _⋆  : (e : RegExp) → RegExp

-- Smart constructors. The proofs involving them are HORRENDOUS.
-- So, for the moment, I am avoiding them.

  _`∣_ : (e₁ e₂ : RegExp) → RegExp
  ∅  `∣ e₂ = e₂
  e₁ `∣ ∅  = e₁
  e₁ `∣ e₂ = e₁ ∣ e₂

  _`∙_ : (e₁ e₂ : RegExp) → RegExp
  ∅  `∙ e₂ = ∅
  e₁ `∙ ∅  = ∅
  e₁ `∙ e₂ = e₁ ∙ e₂

  _`⋆ : RegExp → RegExp
  ∅ `⋆ = ∅
  e `⋆ = e ⋆

-- Extra notions which can be encoded using the existing language

  _+ : (e : RegExp) → RegExp
  e + = e ∙ e ⋆

  _⁇ : (e : RegExp) → RegExp
  e ⁇ = ε ∣ e

  open import Data.Sum
  open import Data.List as List using (List ; [] ; _∷_)

  infix 3 _∈_
  data _∈_ : (xs : List Alphabet) (e : RegExp) → Set where
    ε     : [] ∈ ε
    ─     : {a : Alphabet} → List.[ a ] ∈ ─
    [_]   : (a : Alphabet) → List.[ a ] ∈ RegExp.[ a ]
    _∣₁_  : {xs : List Alphabet} {e : RegExp} (pr : xs ∈ e) (f : RegExp) → xs ∈ e ∣ f
    _∣₂_  : {xs : List Alphabet} (e : RegExp) {f : RegExp} (pr : xs ∈ f) → xs ∈ e ∣ f
    _∙_⇚_ : {xs ys zs : List Alphabet} {e f : RegExp} →
            xs ∈ e → ys ∈ f → zs ≡ xs List.++ ys → zs ∈ e ∙ f
    _⋆    : {xs : List Alphabet} {e : RegExp} →
            xs ∈ ε ∣ e ∙ e ⋆ → xs ∈ e ⋆

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
  e₁ ∣ e₂ ⟪ a = (e₁ ⟪ a) ∣ (e₂ ⟪ a)
  e₁ ∙ e₂ ⟪ a = dec (hasEmpty e₁)
                (const $ ((e₁ ⟪ a) ∙ e₂) ∣ (e₂ ⟪ a))
                (const $ (e₁ ⟪ a) ∙ e₂)
  e ⋆     ⟪ a = (e ⟪ a) ∙ (e ⋆)

  ⟪-sound : (x : Alphabet) (xs : List Alphabet) (e : RegExp) →
            xs ∈ e ⟪ x → x ∷ xs ∈ e
  ⟪-sound x xs ∅ ()
  ⟪-sound x xs ε ()
  ⟪-sound x .[] ─ ε = ─
  ⟪-sound x xs [ a ] pr with x ≟ a
  ⟪-sound x .[] [ .x ] ε | yes refl = [ x ]
  ⟪-sound x xs [ a ] () | no ¬p
  ⟪-sound x xs (e ∣ f) (pr ∣₁ .(f ⟪ x)) = ⟪-sound x xs e pr ∣₁ f
  ⟪-sound x xs (e ∣ f) (.(e ⟪ x) ∣₂ pr) = e ∣₂ ⟪-sound x xs f pr
  ⟪-sound x xs (e ∙ f) pr with hasEmpty e
  ⟪-sound x ._ (e ∙ f) ((pr₁ ∙ pr₂ ⇚ refl) ∣₁ .(f ⟪ x)) | yes p = ⟪-sound x _ e pr₁ ∙ pr₂ ⇚ refl
  ⟪-sound x xs (e ∙ f) (.((e ⟪ x) ∙ f) ∣₂ pr)           | yes p = p ∙ ⟪-sound x xs f pr ⇚ refl
  ⟪-sound x ._ (e ∙ f) (pr₁ ∙ pr₂ ⇚ refl)               | no ¬p = ⟪-sound x _ e pr₁ ∙ pr₂ ⇚ refl
  ⟪-sound x ._ (e ⋆) (pr₁ ∙ pr₂ ⇚ refl) = (ε ∣₂ (⟪-sound x _ e pr₁ ∙ pr₂ ⇚ refl)) ⋆

  ⟪-complete : (x : Alphabet) (xs : List Alphabet) (e : RegExp) →
               x ∷ xs ∈ e → xs ∈ e ⟪ x
  ⟪-complete x .[] .─ ─ = ε
  ⟪-complete x .[] .([ x ]) [ .x ] with x ≟ x
  ⟪-complete x .[] .([ x ]) [ .x ] | yes p = ε
  ⟪-complete x .[] .([ x ]) [ .x ] | no ¬p = ⊥-elim (¬p refl)
  ⟪-complete x xs ._ (pr ∣₁ f) = ⟪-complete x xs _ pr ∣₁ (f ⟪ x)
  ⟪-complete x xs ._ (e ∣₂ pr) = (e ⟪ x) ∣₂ ⟪-complete x xs _ pr
  ⟪-complete x xs (e ∙ f) (pr ∙ pr₁ ⇚ x₁) with hasEmpty e
  ⟪-complete x xs (e ∙ f) (_∙_⇚_ {[]} pr₁ pr₂ refl)        | yes p = _ ∣₂ ⟪-complete x _ f pr₂
  ⟪-complete x ._ (e ∙ f) (_∙_⇚_ {.x ∷ ys} pr₁ pr₂ refl)   | yes p = (⟪-complete x _ e pr₁ ∙ pr₂ ⇚ refl) ∣₁ _
  ⟪-complete x xs (e ∙ f) (_∙_⇚_ {[]}     {zs} pr₁ pr₂ eq) | no ¬p = ⊥-elim (¬p pr₁)
  ⟪-complete x ._ (e ∙ f) (_∙_⇚_ {.x ∷ ys} pr₁ pr₂ refl)   | no ¬p = ⟪-complete x _ e pr₁ ∙ pr₂ ⇚ refl
  ⟪-complete x xs ._ (() ∣₁ ._ ⋆)
  ⟪-complete x xs ._ (.ε ∣₂ _∙_⇚_ {[]} pr₁ pr₂ refl ⋆)      = ⟪-complete x xs _ pr₂
  ⟪-complete x ._ ._ (.ε ∣₂ _∙_⇚_ {.x ∷ ys} pr₁ pr₂ refl ⋆) = ⟪-complete x _ _ pr₁ ∙ pr₂ ⇚ refl

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

module ExampleNat where

  open import Data.Nat as Nat
  module RE = RegularExp ℕ Nat._≟_
  open RE

  0s : RegExp
  0s = [ 0 ] +

  0s1s2s : RegExp
  0s1s2s = 0s ∙ ([ 1 ] ⋆) ∙ ([ 2 ] ⋆)

  open import Data.List

  test : Dec (Substring 0s1s2s (1 ∷ 2 ∷ 0 ∷ 2 ∷ 2 ∷ 0 ∷ 1 ∷ 2 ∷ []))
  test = substring 0s1s2s (1 ∷ 2 ∷ 0 ∷ 2 ∷ 2 ∷ 0 ∷ 1 ∷ 2 ∷ [])

module ExampleString where

  open import Data.Char   as Chr
  open import Data.String as Str
  open import Data.List   as List
  module RE = RegularExp Char Chr._≟_
  open RE
  open import Data.Nat

  lit : (str : String) → RegExp
  lit = List.foldr (_∙_ ∘ RE.[_]) ε ∘ Str.toList

  coloUr : RegExp
  coloUr = lit "colo" ∙ (lit "u" ⁇) ∙ lit "r"

  test : Dec $ Substring coloUr $ Str.toList "green is a nice colour, isn't it?"
  test = substring coloUr $ Str.toList "green is a nice colour, isn't it?"

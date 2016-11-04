module linear.Usage.Erasure where

open import Level
open import Data.Nat hiding (_⊔_)
open import Data.Vec  as Vec hiding (_∷ʳ_)
open import Data.List as List hiding (_∷ʳ_)
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality as PEq using (_≡_)

open import linear.Type
open import linear.Scope as Sc
open import linear.Context as C
open import linear.Context.Pointwise hiding (sym)
open import linear.Usage as U
open import linear.Usage.Consumption as UC hiding (divide)
open import linear.Usage.Pointwise as UP hiding (sym)

⌊_⌋ : {n : ℕ} {γ : Context n} {Γ Δ : Usages γ} → Γ ⊆ Δ →
      Σ[ k ∈ ℕ ] Σ[ m ∈ Sc.Mergey k n ]
      Σ[ δ ∈ Context k ] Σ[ M ∈ C.Mergey m ]
      Σ[ 𝓜 ∈ U.Mergey M ] Σ[ eq ∈ Context[ _≡_ ] γ (δ C.⋈ M) ]
      coerce eq Γ ─ coerce eq Δ ≡ [[ δ ]] U.⋈ 𝓜 ─ ]] δ [[ U.⋈ 𝓜
⌊ []      ⌋ = , , , , finish , [] , []
⌊ ─∷ inc  ⌋ =
  let (k , m , δ , M , 𝓜 , eq , usg) = ⌊ inc ⌋
  in k , insert m , δ , insert _ M , insert (U.[ _ ]) 𝓜 , PEq.refl ∷ eq , (─∷ usg)
⌊ σ ∷ inc ⌋ =
  let (k , m , δ , M , 𝓜 , eq , usg) = ⌊ inc ⌋
  in , , _ ∷ _ , , copy 𝓜 , PEq.refl ∷ eq , σ ∷ usg

used : {n : ℕ} {γ : Context n} {Γ Δ : Usages γ} → Γ ⊆ Δ → List Type
used []      = []
used (─∷ γ)  = used γ
used (σ ∷ γ) = σ ∷ used γ

used-refl : {n : ℕ} {γ : Context n} {Γ : Usages γ} (inc : Γ ⊆ Γ) → used inc ≡ []
used-refl []       = PEq.refl
used-refl (─∷ inc) = used-refl inc

used-all : {n : ℕ} {γ : Context n} (pr : [[ γ ]] ⊆ ]] γ [[) → used pr ≡ toList γ
used-all []      = PEq.refl
used-all (σ ∷ γ) = PEq.cong (σ ∷_) (used-all γ)

used-++ : {k l : ℕ} {γ : Context k} {δ : Context l} {Γ Γ′ : Usages γ} {Δ Δ′ : Usages δ}
          (incΓ : Γ ⊆ Γ′) (incΔ : Δ ⊆ Δ′) →
          used (incΓ UC.++ incΔ) ≡ used incΓ List.++ used incΔ
used-++ []         incΔ = PEq.refl
used-++ (─∷ incΓ)  incΔ = used-++ incΓ incΔ
used-++ (a ∷ incΓ) incΔ = PEq.cong (a ∷_) (used-++ incΓ incΔ)


toList-++ : {k l : ℕ} (xs : Context k) (ys : Context l) →
            toList (xs Vec.++ ys) ≡ toList xs List.++ toList ys
toList-++ []       ys = PEq.refl
toList-++ (x ∷ xs) ys = PEq.cong (x ∷_) (toList-++ xs ys)

infix 1 _++_≅_
data _++_≅_ {A : Set} : (xs ys zs : List A) → Set where
  []   : [] ++ [] ≅ []
  _∷ˡ_ : (a : A) {xs ys zs : List A} (as : xs ++ ys ≅ zs) → a ∷ xs ++ ys ≅ a ∷ zs
  _∷ʳ_ : (a : A) {xs ys zs : List A} (as : xs ++ ys ≅ zs) → xs ++ a ∷ ys ≅ a ∷ zs  

sym : {A : Set} {xs ys zs : List A} → xs ++ ys ≅ zs → ys ++ xs ≅ zs
sym []        = []
sym (x ∷ˡ xs) = x ∷ʳ sym xs
sym (x ∷ʳ xs) = x ∷ˡ sym xs


divide : {n : ℕ} {γ : Context n} {Γ Δ θ : Usages γ} (p : Γ ⊆ Δ) (q : Δ ⊆ θ) (pq : Γ ⊆ θ) →
         used p ++ used q ≅ used pq
divide []      []      []        = []
divide (─∷ p)  (─∷ q)  (─∷ pq)   = divide p q pq
divide (─∷ p)  (a ∷ q) (.a ∷ pq) = a ∷ʳ divide p q pq
divide (a ∷ p) (─∷ q)  (.a ∷ pq) = a ∷ˡ divide p q pq

_++ʳ_ : {A : Set} {xs ys zs : List A} (ts : List A) (eq : xs ++ ys ≅ zs) →
        xs ++ ts List.++ ys ≅ ts List.++ zs
[]       ++ʳ eq = eq
(t ∷ ts) ++ʳ eq = t ∷ʳ (ts ++ʳ eq)

trivial : {A : Set} {xs ys : List A} → xs ++ ys ≅ xs List.++ ys
trivial {xs = []}     {[]}     = []
trivial {xs = []}     {y ∷ ys} = y ∷ʳ trivial
trivial {xs = x ∷ xs}          = x ∷ˡ trivial

module linear.Usage.Erasure where

open import Level
open import Data.Nat hiding (_⊔_)
open import Data.Vec as Vec
open import Data.Product
open import Relation.Binary.PropositionalEquality as PEq

open import linear.Type
open import linear.Scope as Sc
open import linear.Context as C
open import linear.Usage as U
open import linear.Usage.Consumption

data Vec[_] {ℓ^A ℓ^B ℓ^R : Level} {A : Set ℓ^A} {B : Set ℓ^B} (R : A → B → Set ℓ^R) :
            {k : ℕ} → Vec A k → Vec B k → Set (ℓ^A ⊔ ℓ^B ⊔ ℓ^R) where
  []  : Vec[ R ] [] []
  _∷_ : {a : A} {b : B} {k : ℕ} {as : Vec A k} {bs : Vec B k} →
        R a b → Vec[ R ] as bs → Vec[ R ] (a ∷ as) (b ∷ bs)

coerce : ∀ {n} {γ : Context n} {k} {m : Sc.Mergey k n}
        {δ : Context k} (M : C.Mergey m) →
         Vec[ _≡_ ] γ (δ C.⋈ M) → Usages γ → Usages (δ C.⋈ M)
coerce             finish       []         []      = []
coerce             finish       (eq ∷ eqs) (S ∷ Γ) = subst Usage eq S ∷ coerce finish eqs Γ
coerce             (insert σ M) (eq ∷ eqs) (S ∷ Γ) = subst Usage eq S ∷ coerce M eqs Γ
coerce {δ = σ ∷ δ} (copy M)     (eq ∷ eqs) (S ∷ Γ) = subst Usage eq S ∷ coerce M eqs Γ

⌊_⌋ : {n : ℕ} {γ : Context n} {Γ Δ : Usages γ} → Γ ⊆ Δ →
      Σ[ k ∈ ℕ ] Σ[ m ∈ Sc.Mergey k n ]
      Σ[ δ ∈ Context k ] Σ[ M ∈ C.Mergey m ]
      Σ[ 𝓜 ∈ U.Mergey M ] Σ[ eq ∈ Vec[ _≡_ ] γ (δ C.⋈ M) ]
      coerce M eq Γ ─ coerce M eq Δ ≡ [[ δ ]] U.⋈ 𝓜 ─ ]] δ [[ U.⋈ 𝓜
⌊ []      ⌋ = , , , , finish , [] , []
⌊ ─∷ inc  ⌋ =
  let (k , m , δ , M , 𝓜 , eq , usg) = ⌊ inc ⌋
  in k , insert m , δ , insert _ M , insert (U.[ _ ]) 𝓜 , PEq.refl ∷ eq , (─∷ usg)
⌊ σ ∷ inc ⌋ =
  let (k , m , δ , M , 𝓜 , eq , usg) = ⌊ inc ⌋
  in , , _ ∷ _ , , copy 𝓜 , PEq.refl ∷ eq , σ ∷ usg

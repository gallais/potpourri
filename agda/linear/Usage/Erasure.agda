module linear.Usage.Erasure where

open import Level
open import Data.Nat hiding (_⊔_)
open import Data.Vec as Vec
open import Data.Product
open import Relation.Binary.PropositionalEquality as PEq

open import linear.Type
open import linear.Scope as Sc
open import linear.Context as C
open import linear.Context.Pointwise
open import linear.Usage as U
open import linear.Usage.Consumption

⌊_⌋ : {n : ℕ} {γ : Context n} {Γ Δ : Usages γ} → Γ ⊆ Δ →
      Σ[ k ∈ ℕ ] Σ[ m ∈ Sc.Mergey k n ]
      Σ[ δ ∈ Context k ] Σ[ M ∈ C.Mergey m ]
      Σ[ 𝓜 ∈ U.Mergey M ] Σ[ eq ∈ Context[ _≡_ ] γ (δ C.⋈ M) ]
      coerce M eq Γ ─ coerce M eq Δ ≡ [[ δ ]] U.⋈ 𝓜 ─ ]] δ [[ U.⋈ 𝓜
⌊ []      ⌋ = , , , , finish , [] , []
⌊ ─∷ inc  ⌋ =
  let (k , m , δ , M , 𝓜 , eq , usg) = ⌊ inc ⌋
  in k , insert m , δ , insert _ M , insert (U.[ _ ]) 𝓜 , PEq.refl ∷ eq , (─∷ usg)
⌊ σ ∷ inc ⌋ =
  let (k , m , δ , M , 𝓜 , eq , usg) = ⌊ inc ⌋
  in , , _ ∷ _ , , copy 𝓜 , PEq.refl ∷ eq , σ ∷ usg

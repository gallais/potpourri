module linear.Usage where

open import Data.Unit
open import Data.Nat as ℕ
open import Data.Fin
open import Data.Product
open import Data.Vec hiding ([_] ; _++_ ; map ; head ; tail)
open import Function
open import linear.Relation.Functional

open import linear.Type
open import linear.Scope as Sc
  hiding (Mergey ; copys ; inserts
        ; Extending
        ; Weakening ; weakFin
        ; Env ; Substituting
        ; Freshey ; withFreshVars)
open import linear.Context as C
  hiding (Mergey ; _⋈_ ; copys ; inserts
         ; _++_ ; ++copys-elim)
open import Relation.Binary.PropositionalEquality

data Usage : (a : Type) → Set where
  [_] : (a : Type) → Usage a
  ]_[ : (a : Type) → Usage a

infixr 5 _∷_ -- _∙_
data Usages : {n : ℕ} (γ : Context n) → Set where
  []  : Usages []
  _∷_ : {n : ℕ} {γ : Context n} {a : Type} → Usage a → Usages γ → Usages (a ∷ γ)

head : {n : ℕ} {γ : Context n} {a : Type} → Usages (a ∷ γ) → Usage a
head (S ∷ _) = S

tail : {n : ℕ} {γ : Context n} {a : Type} → Usages (a ∷ γ) → Usages γ
tail (_ ∷ Γ) = Γ

infixr 4 _++_
_++_ : {m n : ℕ} {γ : Context m} {δ : Context n}
       (Γ : Usages γ) (Δ : Usages δ) → Usages (γ C.++ δ)
[]    ++ Δ = Δ
x ∷ Γ ++ Δ = x ∷ (Γ ++ Δ)

infix 3 _⊢_∈[_]⊠_
data _⊢_∈[_]⊠_ : {n : ℕ} {γ : Context n} (Γ : Usages γ) (k : Fin n) (a : Type) (Δ : Usages γ) → Set where
  z : {n : ℕ} {γ : Context n} {Γ : Usages γ} {a : Type} → [ a ] ∷ Γ ⊢ zero ∈[ a ]⊠ ] a [ ∷ Γ
  s_ : {n : ℕ} {γ : Context n} {k : Fin n} {Γ Δ : Usages γ} {a b : Type} {u : Usage b} →
       Γ ⊢ k ∈[ a ]⊠ Δ → u ∷ Γ ⊢ suc k ∈[ a ]⊠ u ∷ Δ

[[_]] : {m  : ℕ} (δ : Context m) → Usages δ
[[ δ ]] = induction Usages [] (λ a _ → [ a ] ∷_) δ

]]_[[ : {m : ℕ} (δ : Context m) → Usages δ
]] δ [[ = induction Usages [] (λ a _ → ] a [ ∷_) δ

data Mergey : {k l : ℕ} {m : Sc.Mergey k l} (M : C.Mergey m) → Set where
  finish : {k : ℕ} → Mergey (finish {k})
  copy   : {k l : ℕ} {m : Sc.Mergey k l} {M : C.Mergey m} (𝓜 : Mergey M) → Mergey (copy M)
  insert : {k l : ℕ} {m : Sc.Mergey k l} {M : C.Mergey m} {a : Type}
           (A : Usage a) (𝓜 : Mergey M) → Mergey (insert a M)

copys : (o : ℕ) {k l : ℕ} {m : Sc.Mergey k l} {M : C.Mergey m} →
        Mergey M → Mergey (C.copys o M)
copys zero    M = M
copys (suc o) M = copy (copys o M)

inserts : {o k l : ℕ} {O : Context o} (𝓞 : Usages O) {m : Sc.Mergey k l} {M : C.Mergey m} →
          Mergey M → Mergey (C.inserts O M)
inserts []      𝓜 = 𝓜
inserts (S ∷ 𝓞) 𝓜 = insert S (inserts 𝓞 𝓜)

infixl 4 _⋈_
_⋈_ : {k l : ℕ} {γ : Context k} {m : Sc.Mergey k l} {M : C.Mergey m}
      (Γ : Usages γ) (𝓜 : Mergey M) → Usages (γ C.⋈ M)
Γ     ⋈ finish     = Γ
A ∷ Γ ⋈ copy M     = A ∷ (Γ ⋈ M)
Γ     ⋈ insert A M = A ∷ (Γ ⋈ M)

⋈ˡ : (ri : Σ[ k ∈ ℕ ] Σ[ l ∈ ℕ ] Σ[ γ ∈ Context k ] Σ[ m ∈ Sc.Mergey k l ]
           Σ[ M ∈ C.Mergey m ] Mergey M × Usages (γ C.⋈ M))
     (ii : ⊤) (o : let (_ , _ , γ , _) = ri in Usages γ) → Set
⋈ˡ (_ , _ , _ , _ , _ , 𝓜 , Γ) ii Γ′ = Γ ≡ (Γ′ ⋈ 𝓜)

⋈ˡ-injective : Functional ⋈ˡ
⋈ˡ-injective (l , .l , γ , .finish , .finish , finish , Γ) eq₁ eq₂ = trans (sym eq₁) eq₂
⋈ˡ-injective (_ , _ , _ ∷ γ , _ , _ , copy 𝓜 , S ∷ Γ) {_} {_} {σ ∷ o₁} {τ ∷ o₂} eq₁ eq₂ =
  cong₂ _∷_ (cong head $ trans (sym eq₁) eq₂)
            (⋈ˡ-injective (_ , _ , _ , _ , _ , 𝓜 , Γ) (cong tail eq₁) (cong tail eq₂))
⋈ˡ-injective (k , _ , γ , _ , _ , insert A 𝓜 , S ∷ Γ) eq₁ eq₂ =
  ⋈ˡ-injective (_ , _ , _ , _ , _ , 𝓜 , Γ) (cong tail eq₁) (cong tail eq₂)


++copys-elim₂ :
  {k l o : ℕ} {m : Sc.Mergey k l} {M : C.Mergey m} {δ : Context o} {γ : Context k}
  (P : {γ : Context (o ℕ.+ l)} → Usages γ → Usages γ → Set)
  (Δ Δ′ : Usages δ) (Γ Γ′ : Usages γ) (𝓜 : Mergey M) →
  P ((Δ ++ Γ) ⋈ copys o 𝓜) ((Δ′ ++ Γ′) ⋈ copys o 𝓜) → P (Δ ++ (Γ ⋈ 𝓜)) (Δ′ ++ (Γ′ ⋈ 𝓜))
++copys-elim₂ P []      []        Γ Γ′ 𝓜 p = p
++copys-elim₂ P (A ∷ Δ) (A′ ∷ Δ′) Γ Γ′ 𝓜 p = ++copys-elim₂ (λ θ θ′ → P (A ∷ θ) (A′ ∷ θ′)) Δ Δ′ Γ Γ′ 𝓜 p

-- We can give an abstract interface to describe these relations
-- by introducing the notion of `Typing`. It exists for `Fin`,
-- `Check` and `Infer`:
Typing : (T : ℕ → Set) → Set₁
Typing T = {n : ℕ} {γ : Context n} (Γ : Usages γ) (t : T n) (σ : Type) (Δ : Usages γ) → Set

-- The notion of 'Usage Weakening' can be expressed for a `Typing`
-- of `T` if it enjoys `Scope Weakening`
Weakening : (T : ℕ → Set) (Wk : Sc.Weakening T) (𝓣 : Typing T) → Set
Weakening T Wk 𝓣 =
  {k l : ℕ} {γ : Context k} {Γ Δ : Usages γ} {m : Sc.Mergey k l} {M : C.Mergey m} {σ : Type}
  {t : T k} (𝓜 : Mergey M) → 𝓣 Γ t σ Δ → 𝓣 (Γ ⋈ 𝓜) (Wk m t) σ (Δ ⋈ 𝓜)
  
-- A first example of a Typing enjoying Usage Weakening: Fin.
TFin : Typing Fin
TFin = _⊢_∈[_]⊠_

weakFin : Weakening Fin Sc.weakFin TFin
weakFin finish        k    = k
weakFin (insert A 𝓜) k     = s (weakFin 𝓜 k)
weakFin (copy 𝓜)     z     = z
weakFin (copy 𝓜)     (s k) = s (weakFin 𝓜 k)

-- Similarly to 'Usage Weakening', the notion of 'Usage Substituting'
-- can be expressed for a `Typing` of `T` if it enjoys `Scope Substituting`

data Env {E : ℕ → Set} (𝓔 : Typing E) : {k l : ℕ} {θ : Context l} (T₁ : Usages θ) 
  (ρ : Sc.Env E k l) (Τ₂ : Usages θ) {γ : Context k} (Γ : Usages γ) → Set where
  []    : {l : ℕ} {θ : Context l} {Τ₁ : Usages θ} → Env 𝓔 Τ₁ [] Τ₁ []
  _∷_   : {a : Type} {k l : ℕ} {θ : Context l} {ρ : Sc.Env E k l} {t : E l} {Τ₁ Τ₂ Τ₃ : Usages θ}
          {γ : Context k} {Γ : Usages γ} (T : 𝓔 Τ₁ t a Τ₂) (R : Env 𝓔 Τ₂ ρ Τ₃ Γ) → Env 𝓔 Τ₁ (t ∷ ρ) Τ₃ ([ a ] ∷ Γ)
  ─∷_   : {a : Type} {k l : ℕ} {ρ : Sc.Env E k l} {t : E l} {θ : Context l} {Τ₁ Τ₂ : Usages θ} {γ : Context k}
          {Γ : Usages γ} → Env 𝓔 Τ₁ ρ Τ₂ Γ → Env 𝓔 Τ₁ (t ∷ ρ) Τ₂ (] a [ ∷ Γ)
  [v]∷_ : {a : Type} {k l : ℕ} {ρ : Sc.Env E k l} {θ : Context l} {Τ₁ Τ₂ : Usages θ} {γ : Context k}
          {Γ : Usages γ} → Env 𝓔 Τ₁ ρ Τ₂ Γ → Env 𝓔 ([ a ] ∷ Τ₁) (v∷ ρ) (] a [ ∷ Τ₂) ([ a ] ∷ Γ)
  ]v[∷_ : {a : Type} {k l : ℕ} {ρ : Sc.Env E k l} {θ : Context l} {Τ₁ Τ₂ : Usages θ} {γ : Context k}
          {Γ : Usages γ} → Env 𝓔 Τ₁ ρ Τ₂ Γ → Env 𝓔 (] a [ ∷ Τ₁) (v∷ ρ) (] a [ ∷ Τ₂) (] a [ ∷ Γ)

       
Substituting : (E T : ℕ → Set) ([_]_ : Sc.Substituting E T) (𝓔 : Typing E) (𝓣 : Typing T) → Set
Substituting E T subst 𝓔 𝓣 =
  {k l : ℕ} {γ : Context k} {Γ Δ : Usages γ} {σ : Type} {t : T k} {ρ : Sc.Env E k l}
  {θ : Context l} {Τ₁ Τ₂ : Usages θ} →
  Env 𝓔 Τ₁ ρ Τ₂ Γ → 𝓣 Γ t σ Δ → ∃ λ Τ₃ → 𝓣 Τ₁ (subst ρ t) σ Τ₃ × Env 𝓔 Τ₃ ρ Τ₂ Δ

[Extending] : (E : ℕ → ℕ → Set) (Ext : Sc.Extending E)
  (𝓔 : {k l : ℕ} {θ : Context l} (T₁ : Usages θ) (ρ : E k l) (Τ₂ : Usages θ) {γ : Context k} (Γ : Usages γ) → Set)
  → Set
[Extending] E Ext 𝓔 =
  {k l o : ℕ} {θ : Context l} {Τ₁ Τ₂ : Usages θ} (δ : Context o) {e : E k l} {γ : Context k} {Γ : Usages γ} →
  𝓔 Τ₁ e Τ₂ Γ → 𝓔 ([[ δ ]] ++ Τ₁) (Ext o e) (]] δ [[ ++ Τ₂) ([[ δ ]] ++ Γ)

]Extending[ : (E : ℕ → ℕ → Set) (Ext : Sc.Extending E)
  (𝓔 : {k l : ℕ} {θ : Context l} (T₁ : Usages θ) (ρ : E k l) (Τ₂ : Usages θ) {γ : Context k} (Γ : Usages γ) → Set)
  → Set
]Extending[ E Ext 𝓔 =
  {k l o : ℕ} {θ : Context l} {Τ₁ Τ₂ : Usages θ} (δ : Context o) {e : E k l} {γ : Context k} {Γ : Usages γ} →
  𝓔 Τ₁ e Τ₂ Γ → 𝓔 (]] δ [[ ++ Τ₁) (Ext o e) (]] δ [[ ++ Τ₂) (]] δ [[ ++ Γ)

record Freshey (E : ℕ → Set) (F : Sc.Freshey E) (𝓔 : Typing E) : Set where
  field
    fresh : {k : ℕ} {γ : Context k} {Γ : Usages γ} (σ : Type) →
            𝓔 ([ σ ] ∷ Γ) (Sc.Freshey.fresh F {k}) σ (] σ [ ∷ Γ)
    weak  : Weakening E (Sc.Freshey.weak F) 𝓔

withFreshVars : {E : ℕ → Set} {𝓔 : Typing E} → [Extending] (Sc.Env E) Sc.withFreshVars (Env 𝓔)
withFreshVars []      ρ = ρ
withFreshVars (a ∷ δ) ρ = [v]∷ withFreshVars δ ρ

withStaleVars : {E : ℕ → Set} {𝓔 : Typing E} → ]Extending[ (Sc.Env E) Sc.withFreshVars (Env 𝓔)
withStaleVars []      ρ = ρ
withStaleVars (a ∷ δ) ρ = ]v[∷ withStaleVars δ ρ

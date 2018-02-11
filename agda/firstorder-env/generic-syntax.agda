module generic-syntax where

open import Level
open import Size
open import Data.List.Base
open import Data.Product as Prod
open import Data.Sum as Sum
open import Function
open import Agda.Builtin.Equality
open import Relation.Nullary

module _ {ℓ^I ℓ^S} {I : Set ℓ^I} where

  infix 1 ∀[_]
  ∀[_] : (I → Set ℓ^S) → Set (ℓ^I ⊔ ℓ^S)
  ∀[ P ] = ∀ {i} → P i

  infixr 2 _∙→_
  _∙→_ : (F G : I → Set ℓ^S) → (I → Set ℓ^S)
  (F ∙→ G) i = F i → G i

  infixr 3 _∙×_
  _∙×_ : (F G : I → Set ℓ^S) → (I → Set ℓ^S)
  (F ∙× G) i = F i × G i

  infixr 4 _∙⊎_
  _∙⊎_ : (F G : I → Set ℓ^S) → (I → Set ℓ^S)
  (F ∙⊎ G) i = F i ⊎ G i

  infix 5 _⊢_
  _⊢_ : (I → I) → (I → Set ℓ^S) → (I → Set ℓ^S)
  (f ⊢ T) i = T (f i)

  infix 6 κ_
  κ_ : Set ℓ^S → (I → Set ℓ^S)
  (κ T) i = T

Ctx : Set → Set
Ctx = List

_─Scoped : Set → Set₁
I ─Scoped = I → Ctx I → Set

module _ {I : Set} where

  data Var : I ─Scoped where
    z : ∀ {σ} →    ∀[           (σ ∷_) ⊢ Var σ ]
    s : ∀ {σ τ} →  ∀[ Var σ ∙→  (τ ∷_) ⊢ Var σ ]

  infixl 4 _,_
  data Env (T : I ─Scoped) : Ctx I → Ctx I → Set where
    []   : ∀ {Δ} → Env T Δ []
    _,_  : ∀ {Δ Γ σ} → Env T Δ Γ → T σ Δ → Env T Δ (σ ∷ Γ)
    wk   : ∀ {Δ Γ σ} → Env T Δ Γ → Env T (σ ∷ Δ) (σ ∷ Γ)
    st   : ∀ {Δ Γ σ} → Env T Δ Γ → Env T (σ ∷ Δ) Γ

  infix 4 _⊇_
  _⊇_ : Ctx I → Ctx I → Set
  _⊇_ = Env Var

  rename : ∀ {Γ Δ σ} → Δ ⊇ Γ → Var σ Γ → Var σ Δ
  rename (_ , v) z     = v
  rename (ρ , _) (s v) = rename ρ v
  rename (wk ρ) z      = z
  rename (wk ρ) (s v)  = s (rename ρ v)
  rename (st ρ)  v     = s (rename ρ v)

  ⊇-refl : ∀ {Γ} → Γ ⊇ Γ
  ⊇-refl {[]}    = []
  ⊇-refl {σ ∷ Γ} = wk ⊇-refl

  infixl 4 _^_
  infixl 5 _^^_
  record _^_ (T : Ctx I → Set) (Γ : Ctx I) : Set where
    constructor _^^_
    field {thinner} : Ctx I
          value     : T thinner
          thinning  : Γ ⊇ thinner
  wk^ : ∀ {T Γ σ} → T ^ Γ → T ^ σ ∷ Γ
  wk^ (t ^^ th) = t ^^ st th

  infixr 6 □_
  □_ : (Ctx I → Set) → (Ctx I → Set)
  (□ T) i = ∀[ _⊇ i ∙→ T ]

  record Thinnable (T : Ctx I → Set) : Set where
    field thin : ∀[ T ∙→ □ T ]
  open Thinnable public

  infixl 4 _vv_
  _vv_ : ∀ {T} → Thinnable T → ∀[ T ^_ ∙→ T ]
  th^T vv t ^^ th = thin th^T t th

  lookup : {T : I ─Scoped} → ∀ {σ Δ Γ} → Env T Δ Γ → Var σ Γ →
           Var σ Δ ⊎ T σ ^ Δ
  lookup (ρ , t) z     = inj₂ (t ^^ ⊇-refl)
  lookup (ρ , t) (s v) = lookup ρ v
  lookup (wk ρ)  z     = inj₁ z
  lookup (wk ρ)  (s v) = Sum.map s wk^ (lookup ρ v)
  lookup (st ρ)  v     = Sum.map s wk^ (lookup ρ v)

  record VarLike (T : I ─Scoped) : Set where
    field thinnable : ∀[ Thinnable ∘′ T ]
          fromVar   : ∀ {σ} → ∀[ Var σ ∙→ T σ ]
  open VarLike public

  ⟦var⟧ : ∀ {T σ Γ Δ} → VarLike T → Env T Δ Γ → Var σ Γ → T σ Δ
  ⟦var⟧ vl^T ρ v = case lookup ρ v of λ where
    (inj₁ v') → fromVar vl^T v'
    (inj₂ t^) → thinnable vl^T vv t^

record Datoid : Set₁ where
  constructor _by_
  field set : Set
        dec : ∀ (s t : set) → Dec (s ≡ t)
open Datoid public

data Desc (I : Set) : Set₁ where
  `σ : (D : Datoid) (d : set D → Desc I) → Desc I
  `X : Ctx I → I → Desc I → Desc I
  `∎ : I → Desc I

module _ {I : Set} where

  record Tag (D : Datoid) (F : set D → I ─Scoped) (σ : I) (Γ : Ctx I) : Set where
    constructor <_>_
    field tag : set D
          val : F tag σ Γ

  ⟦_⟧ : Desc I → (Ctx I → I ─Scoped) → I ─Scoped
  ⟦ `σ D d   ⟧ X = Tag D (λ tg → ⟦ d tg ⟧ X)
  ⟦ `X Δ j d ⟧ X = λ i → X Δ j ∙× ⟦ d ⟧ X i
  ⟦ `∎ j     ⟧ X = λ i → κ (i ≡ j)

  fmap : ∀ d {F G : Ctx I → I ─Scoped} {σ Γ Δ} →
         (f2g : ∀ Θ {σ} → F Θ σ Γ → G Θ σ Δ) →
         ⟦ d ⟧ F σ Γ → ⟦ d ⟧ G σ Δ
  fmap (`σ D d)    f2g (< a > t)  = < a > fmap (d a) f2g t
  fmap (`X Δ j d)  f2g (x , t)    = f2g Δ x , fmap d f2g t
  fmap (`∎ j)      f2g eq         = eq

  dBr : I ─Scoped → Ctx I → I ─Scoped
  dBr T Δ i = (Δ ++_) ⊢ T i

  data Tm (d : Desc I) : Size → I ─Scoped where
    V[_] : ∀ {i σ Γ} → Var σ Γ → Tm d (↑ i) σ Γ
    T[_] : ∀ {i σ Γ} → ⟦ d ⟧ (dBr (Tm d i)) σ Γ → Tm d (↑ i) σ Γ

  Krp : (V C : I ─Scoped) → Ctx I → I ─Scoped
  Krp V C []  σ = C σ
  Krp V C Δ   σ = □ (flip (Env V) Δ ∙→ C σ)

  record Sem (d : Desc I) (V C : I ─Scoped) : Set where
    field vl^V : VarLike V
          var  : ∀ {σ} → ∀[ V σ                ∙→ C σ ]
          alg  : ∀ {σ} → ∀[ ⟦ d ⟧ (Krp V C) σ  ∙→ C σ ]

    Cmp : (T C : I ─Scoped) → Ctx I → Ctx I → Set
    Cmp T C Δ Γ = ∀ {σ} → T σ Γ → C σ Δ

    sem : ∀ {Δ Γ i} → Env V Δ Γ → Cmp (Tm d i) C Δ Γ
    krp : ∀ {Δ Γ i} → Env V Δ Γ → ∀ Θ → Cmp (dBr (Tm d i) Θ) (Krp V C Θ) Δ Γ

    sem ρ V[ v ] = var (⟦var⟧ vl^V ρ v)
    sem ρ T[ t ] = alg (fmap d (krp ρ) t)

    krp ρ []        t = sem ρ t
    krp ρ Θ@(_ ∷ _) t = λ ρ′ vs → sem {!!} t

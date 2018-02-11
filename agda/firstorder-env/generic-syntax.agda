module generic-syntax where

open import Level
open import Size
open import Data.List.Base
open import Data.Product as Prod
open import Data.Sum as Sum
open import Function
open import Relation.Binary.PropositionalEquality
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

  lvlUp : ∀ {σ Δ} → ∀[ Var σ ∙→ (_++ Δ) ⊢ Var σ ]
  lvlUp z     = z
  lvlUp (s v) = s (lvlUp v)

  infix 4 _≤_
  data _≤_ : Ctx I → Ctx I → Set where
    qed : ∀ {Γ} → Γ ≤ Γ
    put : ∀ {Γ Δ σ} → Γ ≤ Δ → Γ ≤ σ ∷ Δ

  _≤++_ : ∀ Δ Γ → Γ ≤ Δ ++ Γ
  []      ≤++ Δ = qed
  (σ ∷ Γ) ≤++ Δ = put (Γ ≤++ Δ)

  lce : ∀ {Γ Δ σ} → Γ ≤ Δ → Var σ Γ → Var σ Δ
  lce qed      v      = v
  lce (put th) v      = s (lce th v)

  cut : ∀ {Γ Δ Θ} → Γ ≤ Δ → Δ ≤ Θ → Γ ≤ Θ
  cut th₁       qed       = th₁
  cut th₁       (put th₂) = put (cut th₁ th₂)

  infixl 4 _^_
  infixl 5 _^^_
  record _^_ (T : Ctx I → Set) (Γ : Ctx I) : Set where
    constructor _^^_
    field {thinner} : Ctx I
          value     : T thinner
          thinning  : thinner ≤ Γ

  infixl 4 _,_
  data Env (T : I ─Scoped) : Ctx I → Ctx I → Set where
    []   : ∀ {Δ}     → Env T [] Δ
    _,_  : ∀ {σ Γ Δ} → Env T Γ Δ → T σ Δ → Env T (σ ∷ Γ) Δ
    shft : ∀ {Γ Θ} Δ → Env T Γ Θ → Env T (Δ ++ Γ) (Δ ++ Θ)
    embd : ∀ {Γ Δ Θ} → Δ ≤ Θ → Env T Γ Δ → Env T Γ Θ

  shift : ∀ {T Γ Δ σ} → Env T Γ Δ → Env T (σ ∷ Γ) (σ ∷ Δ)
  shift (shft Δ ρ) = shft (_ ∷ Δ) ρ
  shift ρ          = shft (_ ∷ []) ρ

  shft-refl : ∀ {T} Γ → Env T Γ Γ
  shft-refl []      = []
  shft-refl (σ ∷ Γ) = shift (shft-refl Γ)

  wk^ : ∀ {T Γ Δ} → Γ ≤ Δ → T ^ Γ → T ^ Δ
  wk^ th₁ (t ^^ th₂) = t ^^ cut th₂ th₁

  map^ : ∀ {T U} → ∀[ T ∙→ U ] → ∀[ T ^_ ∙→ U ^_ ]
  map^ f (t ^^ th) = f t ^^ th

  infixr 6 □_
  □_ : (Ctx I → Set) → (Ctx I → Set)
  (□ T) i = ∀[ i ≤_ ∙→ T ]

  record Thinnable (T : Ctx I → Set) : Set where
    field thin : ∀[ T ∙→ □ T ]
  open Thinnable public

  th^Var : ∀ {σ} → Thinnable (Var σ)
  thin th^Var v th = lce th v

  th^Env : ∀ {T Γ} → Thinnable (Env T Γ)
  thin th^Env (embd th₁ ρ) th = embd (cut th₁ th) ρ
  thin th^Env ρ            th = embd th ρ

  infixl 4 _vv_
  _vv_ : ∀ {T} → Thinnable T → ∀[ T ^_ ∙→ T ]
  th^T vv t ^^ th = thin th^T t th

  lookup : {T : I ─Scoped} → ∀ {σ Δ Γ} → Env T Γ Δ → Var σ Γ →
           (Var σ ∙⊎ T σ) ^ Δ
  lookup [] ()
  lookup (ρ , t)           z     = inj₂ t ^^ qed
  lookup (ρ , t)           (s v) = lookup ρ v
  lookup (shft [] ρ)       v     = lookup ρ v
  lookup (shft (σ ∷ _) ρ)  z     = inj₁ z ^^ qed
  lookup (shft (_ ∷ Δ) ρ)  (s v) = wk^ (put qed) (lookup (shft Δ ρ) v)
  lookup (embd th ρ)       v     = wk^ th (lookup ρ v)

  data Ass (V : I ─Scoped) : Ctx I → Ctx I → Set where
    []   : ∀ {Δ}     → Ass V [] Δ
    _,_  : ∀ {σ Γ Δ} → Ass V Γ Δ → V σ Δ → Ass V (σ ∷ Γ) Δ

  _,,_ : ∀ {V Γ Δ Θ} → Ass V Γ Θ → Env V Δ Θ → Env V (Γ ++ Δ) Θ
  []       ,, ρ = ρ
  (vs , v) ,, ρ = (vs ,, ρ) , v

  record VarLike (T : I ─Scoped) : Set where
    field thinnable : ∀[ Thinnable ∘′ T ]
          fromVar   : ∀ {σ} → ∀[ Var σ ∙→ T σ ]

    ass : ∀ Γ {Δ} → (∀ {σ} → Var σ Γ → Var σ Δ) → Ass T Γ Δ
    ass []      f = []
    ass (σ ∷ Γ) f = ass Γ (f ∘′ s) , fromVar (f z)
  open VarLike public

  vl^Var : VarLike Var
  thinnable  vl^Var = th^Var
  fromVar    vl^Var = id

  ⟦var⟧ : ∀ {T σ Γ Δ} → VarLike T → Env T Γ Δ → Var σ Γ → T σ Δ
  ⟦var⟧ vl^T ρ v = case lookup ρ v of λ where
    (inj₁ w ^^ th) → fromVar vl^T (lce th w)
    (inj₂ t ^^ th) → thinnable vl^T vv (t ^^ th)

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

  infixr 3 <_>_
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

  infix 2 V[_] T[_]
  data Tm (d : Desc I) : Size → I ─Scoped where
    V[_] : ∀ {i σ Γ} → Var σ Γ → Tm d (↑ i) σ Γ
    T[_] : ∀ {i σ Γ} → ⟦ d ⟧ (dBr (Tm d i)) σ Γ → Tm d (↑ i) σ Γ

  Krp : (V C : I ─Scoped) → Ctx I → I ─Scoped
  Krp V C []  σ = C σ
  Krp V C Δ   σ = □ (Ass V Δ ∙→ C σ)

  record Sem (d : Desc I) (V C : I ─Scoped) : Set where
    field vl^V : VarLike V
          var  : ∀ {σ} → ∀[ V σ                ∙→ C σ ]
          alg  : ∀ {σ} → ∀[ ⟦ d ⟧ (Krp V C) σ  ∙→ C σ ]

    Cmp : (T C : I ─Scoped) → Ctx I → Ctx I → Set
    Cmp T C Γ Δ = ∀ {σ} → T σ Γ → C σ Δ

    sem : ∀ {Δ Γ i} → Env V Γ Δ → Cmp (Tm d i) C Γ Δ
    krp : ∀ {Δ Γ i} → Env V Γ Δ → ∀ Θ → Cmp (dBr (Tm d i) Θ) (Krp V C Θ) Γ Δ

    sem ρ V[ v ] = var (⟦var⟧ vl^V ρ v)
    sem ρ T[ t ] = alg (fmap d (krp ρ) t)

    krp ρ []        t = sem ρ t
    krp ρ Θ@(_ ∷ _) t = λ th vs → sem (vs ,, thin th^Env ρ th) t

  reify : ∀ {d V Γ} → VarLike V → ∀ Δ {σ} → Krp V (Tm d ∞) Δ σ Γ → dBr (Tm d ∞) Δ σ Γ
  reify vl^V []        kr = kr
  reify vl^V Δ@(_ ∷ _) kr = kr (Δ ≤++ _) (ass vl^V Δ lvlUp)

  Ren : ∀ d → Sem d Var (Tm d ∞)
  Sem.vl^V  (Ren d) = vl^Var
  Sem.var   (Ren d) = V[_]
  Sem.alg   (Ren d) = T[_] ∘′ fmap d (reify vl^Var)

  th^Tm : ∀ {d σ} → Thinnable (Tm d ∞ σ)
  thin th^Tm t th = Sem.sem (Ren _) (embd th (shft-refl _)) t

  vl^Tm : ∀ {d} → VarLike (Tm d ∞)
  thinnable  vl^Tm = th^Tm
  fromVar    vl^Tm = V[_]

  Sub : ∀ d → Sem d (Tm d ∞) (Tm d ∞)
  Sem.vl^V  (Sub d) = vl^Tm
  Sem.var   (Sub d) = id
  Sem.alg   (Sub d) = T[_] ∘′ fmap d (reify vl^Tm)


infixr 10 _⇒_
data ty : Set where
  α   : ty
  _⇒_ : ty → ty → ty

ty-dec : (σ τ : ty) → Dec (σ ≡ τ)
ty-dec α         α         = yes refl
ty-dec (σ₁ ⇒ τ₁) (σ₂ ⇒ τ₂) with ty-dec σ₁ σ₂ | ty-dec τ₁ τ₂
... | yes eqσ | yes eqτ = yes (cong₂ _⇒_ eqσ eqτ)
... | _ | _ = no absurd where postulate absurd : _
ty-dec _ _ = no absurd where postulate absurd : _

data STLC : Set where
  lam app : ty → ty → STLC

STLC-dec : (s t : STLC) → Dec (s ≡ t)
STLC-dec (lam σ₁ τ₁) (lam σ₂ τ₂) with ty-dec σ₁ σ₂ | ty-dec τ₁ τ₂
... | yes eqσ | yes eqτ = yes (cong₂ lam eqσ eqτ)
... | _ | _ = no absurd where postulate absurd : _
STLC-dec (app σ₁ τ₁) (app σ₂ τ₂) with ty-dec σ₁ σ₂ | ty-dec τ₁ τ₂
... | yes eqσ | yes eqτ = yes (cong₂ app eqσ eqτ)
... | _ | _ = no absurd where postulate absurd : _
STLC-dec _ _ = no absurd where postulate absurd : _

Stlc : Datoid
set Stlc = STLC
dec Stlc = STLC-dec

`STLC : Desc ty
`STLC = `σ Stlc $ λ where
  (lam σ τ) → `X (σ ∷ []) τ (`∎ (σ ⇒ τ))
  (app σ τ) → `X [] (σ ⇒ τ) (`X [] σ (`∎ τ))

infixr 5 `λ_
infixl 6 _`$_
pattern `λ_ b    = T[ < lam _ _ > b , refl ]
pattern _`$_ f t = T[ < app _ _ > f , (t , refl) ]

`id : ∀ {σ} → Tm `STLC ∞ (σ ⇒ σ) []
`id = `λ V[ z ]

`K : ∀ {σ τ} → Tm `STLC ∞ (σ ⇒ τ ⇒ σ) []
`K = `λ `λ V[ s z ]

`S : ∀ {σ τ ν} → Tm `STLC ∞ ((σ ⇒ τ ⇒ ν) ⇒ (σ ⇒ τ) ⇒ (σ ⇒ ν)) []
`S = `λ `λ `λ V[ s (s z) ] `$ V[ z ] `$ (V[ s z ] `$ V[ z ])

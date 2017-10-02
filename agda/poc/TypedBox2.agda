module poc.TypedBox2 where

open import Agda.Builtin.List
open import Data.Product
open import Function

data Ty :      Set
data FO : Ty → Set

infixr 5 _`→_
data Ty where
  `1 `2   : Ty
  _`→_    : Ty → Ty → Ty
  C[_,_]  : {σ τ : Ty} → FO σ → FO τ → Ty

data FO where
  `1   : FO `1
  `2   : FO `2

module _ {I : Set} where

  infixr 2 κ_
  κ_ : Set → (I → Set)
  (κ A) i = A

  infixr 1 _∙→_
  _∙→_ : (I → Set) → (I → Set) → (I → Set)
  (A ∙→ B) i = A i → B i

  infix 0 [_]
  [_] : (I → Set) → Set
  [ A ] = ∀ {i} → A i

  infix 4 _⊢_
  _⊢_ : (I → I) → (I → Set) → (I → Set)
  (f ⊢ A) i = A (f i)

  □ : (I → I → Set) → (I → Set) → (I → Set)
  (□ R A) i = ∀ {j} → R i j → A j

module _ {I : Set} where

  data Var : I → List I → Set where
    z : {σ : I}   → [           (σ ∷_) ⊢ Var σ ]
    s : {σ τ : I} → [ Var σ ∙→  (τ ∷_) ⊢ Var σ ]

module _ {A : Set} where

 data Cover : List A → List A → List A → Set where
   []   : Cover [] [] []
   _∷_  : (a : A) {as bs cs : List A} →
          Cover as bs cs → Cover (a ∷ as) (a ∷ bs) (a ∷ cs)
   _∷ˡ_ : (a : A) {as bs cs : List A} →
          Cover as bs cs → Cover (a ∷ as) bs (a ∷ cs)
   _∷ʳ_ : (a : A) {as bs cs : List A} →
          Cover as bs cs → Cover as (a ∷ bs) (a ∷ cs)

 left : {as : List A} → Cover as [] as
 left {as = []}     = []
 left {as = a ∷ as} = a ∷ˡ left

 right : {as : List A} → Cover [] as as
 right {as = []}     = []
 right {as = a ∷ as} = a ∷ʳ right

 data OPE : List A → List A → Set where
   []   : {as : List A} → OPE [] as
   _∷_  : (a : A) {as bs : List A} → OPE as bs → OPE (a ∷ as) (a ∷ bs)
   _∷ʳ_ : (a : A) {as bs : List A} → OPE as bs → OPE as (a ∷ bs)

 refl : {as : List A} → OPE as as
 refl {as = []}     = []
 refl {as = a ∷ as} = a ∷ refl

 trans : {as bs cs : List A} → OPE as bs → OPE bs cs → OPE as cs
 trans []        p        = []
 trans o         (a ∷ʳ p) = a ∷ʳ trans o p
 trans (.a ∷ o)  (a ∷ p)  = a ∷ trans o p
 trans (.a ∷ʳ o) (a ∷ p)  = a ∷ʳ trans o p

 merge : {as bs cs : List A} → OPE as cs → OPE bs cs →
         ∃ λ ds → Cover as bs ds × OPE ds cs
 merge []       q         = _ , right , q
 merge p        []        = _ , left  , p
 merge (a ∷ p)  (.a ∷ q)  = case merge p q of λ where (_ , c , o) → _ , a ∷ c  , a ∷ o
 merge (a ∷ p)  (.a ∷ʳ q) = case merge p q of λ where (_ , c , o) → _ , a ∷ˡ c , a ∷ o
 merge (a ∷ʳ p) (.a ∷ q)  = case merge p q of λ where (_ , c , o) → _ , a ∷ʳ c , a ∷ o
 merge (a ∷ʳ p) (.a ∷ʳ q) = case merge p q of λ where (_ , c , o) → _ , c      , a ∷ʳ o

 Thinnable : (List A → Set) → Set
 Thinnable T = [ T ∙→ □ OPE T ]

 th^Var : ∀ {a} → Thinnable (Var a)
 th^Var () []
 th^Var z     (a ∷  ρ) = z
 th^Var (s v) (a ∷  ρ) = s (th^Var v ρ)
 th^Var v     (a ∷ʳ ρ) = s (th^Var v ρ)

 th^□ : {T : List A → Set} → Thinnable (□ OPE T)
 th^□ t o p = t (trans o p)

 record Emb (E : List A → Set) (Δ : List A) : Set where
   constructor `emb
   field {context} : List A
         value     : E context
         ope       : OPE context Δ
 map^Emb : {E F : List A → Set} → [ E ∙→ F ] → [ Emb E ∙→ Emb F ]
 map^Emb f (`emb e pr) = `emb (f e) pr

 join^Emb : {E : List A → Set} → [ Emb (Emb E) ∙→ Emb E ]
 join^Emb (`emb (`emb e ope₂) ope₁) = `emb e (trans ope₂ ope₁)

 th^Emb : {E : List A → Set} → Thinnable (Emb E)
 th^Emb (`emb v ope) ρ = `emb v (trans ope ρ)

 infix 1 _─Env
 record _─Env (Γ : List A) (𝓥 : A → List A → Set) (Δ : List A) : Set where
   constructor pack
   field lookup : {a : A} → Var a Γ → 𝓥 a Δ
 open _─Env public

 ε : {𝓥 : A → List A → Set} {Δ : List A} → ([] ─Env) 𝓥 Δ
 lookup ε ()

 _∙_ : {Γ Δ : List A} {𝓥 : A → List A → Set} {a : A} →
       (Γ ─Env) 𝓥 Δ → 𝓥 a Δ → (a ∷ Γ ─Env) 𝓥 Δ
 lookup (ρ ∙ v) z     = v
 lookup (ρ ∙ v) (s k) = lookup ρ k

 th^Env : {𝓥 : A → List A → Set} {Γ : List A} →
          ((a : A) → Thinnable (𝓥 a)) → Thinnable ((Γ ─Env) 𝓥)
 lookup (th^Env th^𝓥 ρ o) k = th^𝓥 _ (lookup ρ k) o


module Language (CUT : Set) where

  data Cn   : Ty → List Ty → Set
  data El   : Ty → List Ty → Set
  data El^□ : Ty → List Ty → Set
  data Hw   : {s t : Ty} → FO s → FO t → List Ty → Set

  data Cn    where
    `lam : {σ τ : Ty}                       →  [ (σ ∷_) ⊢ Cn τ  ∙→  Cn (σ `→ τ)  ]
    `hdw : {s t : Ty} {σ : FO s} {τ : FO t} →  [ Hw σ τ         ∙→  Cn (s `→ t)  ]
    `neu : {σ : Ty}                         →  [ El^□ σ         ∙→  Cn σ         ]
    `unt :                                     [                    Cn `1        ]
    `one :                                     [                    Cn `2        ]
    `two :                                     [                    Cn `2        ]

  data El^□  where
    `box : {s t : Ty} {σ : FO s} {τ : FO t} →  [ El (s `→ t)    ∙→ El^□ C[ σ , τ ]  ]
    `run : {s t : Ty} {σ : FO s} {τ : FO t} →  [ El C[ σ , τ ]  ∙→ El^□ (s `→ t)    ]
    `neu : {σ : Ty}                         →  [ El σ           ∙→ El^□ σ           ]

  data El    where
    `var : {σ : Ty}    → [ Var σ                    ∙→ El σ ]
    `cut : {σ : Ty}    → [ κ CUT ∙→ Cn σ            ∙→ El σ ]
    `hdw : {s t : Ty} {σ : FO s} {τ : FO t} →  [ κ CUT ∙→ Hw σ τ ∙→ El C[ σ , τ ] ]
    `app : {σ τ : Ty}  → [ El^□ (σ `→ τ) ∙→ Cn σ    ∙→ El τ ]
    `ift : {σ : Ty}    → [ El^□ `2 ∙→ Cn σ ∙→ Cn σ  ∙→ El σ ]

  data Hw    where
    `neu : {s t : Ty} {σ : FO s} {τ : FO t} →  [ El^□ C[ σ , τ ]  ∙→ Hw σ τ ]
    `seq : {s t u : Ty} {σ : FO s} {τ : FO t} {ν : FO u} →
           [ Hw σ τ ∙→ Hw τ ν ∙→ Hw σ ν ]
    `wir : {s : Ty} {σ : FO s} → [ Hw σ   σ ]
    `one : [ Hw `1 `2 ]
    `two : [ Hw `1 `2 ]
    `ift : {s t : Ty} {σ : FO s} {τ : FO t} → [ Hw σ `2 ∙→ Hw σ τ ∙→ Hw σ τ ∙→ Hw σ τ ]


  th^Cn   : ∀ {σ}   → Thinnable (Cn σ)
  th^El   : ∀ {σ}   → Thinnable (El σ)
  th^El^□ : ∀ {σ}   → Thinnable (El^□ σ)
  th^Hw   : ∀ {s t} {σ : FO s} {τ : FO t} → Thinnable (Hw σ τ)

  th^Cn (`lam b) ρ = `lam (th^Cn b (_ ∷ ρ))
  th^Cn (`hdw c) ρ = `hdw (th^Hw c ρ)
  th^Cn (`neu t) ρ = `neu (th^El^□ t ρ)
  th^Cn `unt     ρ = `unt
  th^Cn `one     ρ = `one
  th^Cn `two     ρ = `two

  th^El (`var v)     ρ = `var (th^Var v ρ)
  th^El (`cut c t)   ρ = `cut c (th^Cn t ρ)
  th^El (`hdw h t)   ρ = `hdw h (th^Hw t ρ)
  th^El (`app f t)   ρ = `app (th^El^□ f ρ) (th^Cn t ρ)
  th^El (`ift b l r) ρ = `ift (th^El^□ b ρ) (th^Cn l ρ) (th^Cn r ρ)

  th^El^□ (`box t) ρ = `box (th^El t ρ)
  th^El^□ (`run t) ρ = `run (th^El t ρ)
  th^El^□ (`neu t) ρ = `neu (th^El t ρ)

  th^Hw (`neu t)     ρ = `neu (th^El^□ t ρ)
  th^Hw (`seq t u)   ρ = `seq (th^Hw t ρ) (th^Hw u ρ)
  th^Hw `wir         ρ = `wir
  th^Hw `one         ρ = `one
  th^Hw `two         ρ = `two
  th^Hw (`ift b l r) ρ = `ift (th^Hw b ρ) (th^Hw l ρ) (th^Hw r ρ)



open Language

open import Data.Unit
open import Data.Empty

module Expr = Language ⊤
module Norm = Language ⊥

⟦_⟧ : Ty → List Ty → Set
⟦ `1         ⟧ = κ ⊤
⟦ `2         ⟧ = Norm.Cn `2
⟦ σ `→ τ     ⟧ = □ OPE (⟦ σ ⟧ ∙→ ⟦ τ ⟧)
⟦ C[ σ , τ ] ⟧ = Norm.Hw σ τ

th^⟦_⟧ : (a : Ty) → Thinnable ⟦ a ⟧
th^⟦ `1         ⟧ = λ _ _ → tt
th^⟦ `2         ⟧ = Norm.th^Cn
th^⟦ σ `→ τ     ⟧ = th^□
th^⟦ C[ σ , τ ] ⟧ = Norm.th^Hw


eval^Cn   : ∀ {σ Γ Δ} → (Γ ─Env) ⟦_⟧ Δ → Expr.Cn   σ Γ → ⟦ σ ⟧ Δ
eval^El   : ∀ {σ Γ Δ} → (Γ ─Env) ⟦_⟧ Δ → Expr.El   σ Γ → ⟦ σ ⟧ Δ
eval^El^□ : ∀ {σ Γ Δ} → (Γ ─Env) ⟦_⟧ Δ → Expr.El^□ σ Γ → ⟦ σ ⟧ Δ
eval^Hw   : ∀ {s t Γ Δ} {σ : FO s} {τ : FO t} → (Γ ─Env) ⟦_⟧ Δ → Expr.Hw σ τ Γ → ⟦ C[ σ , τ ] ⟧ Δ

eval^Cn ρ (`lam b) = λ σ v → eval^Cn (th^Env th^⟦_⟧ ρ σ ∙ v) b
eval^Cn ρ (`hdw t) = {!eval^Hw ρ r!}
eval^Cn ρ (`neu t) = eval^El^□ ρ t
eval^Cn ρ `unt     = tt
eval^Cn ρ `one     = `one
eval^Cn ρ `two     = `two

eval^El ρ (`var v)     = lookup ρ v
eval^El ρ (`cut c t)   = eval^Cn ρ t
eval^El ρ (`hdw c t)   = eval^Hw ρ t
eval^El ρ (`app f t)   = eval^El^□ ρ f refl (eval^Cn ρ t)
eval^El ρ (`ift b l r) with eval^El^□ ρ b
... | `one   = eval^Cn ρ l
... | `two   = eval^Cn ρ r
... | `neu t = {!!}

eval^El^□ ρ (`box t) = {!!}
eval^El^□ ρ (`run c) = {!!}
eval^El^□ ρ (`neu t) = eval^El ρ t

eval^Hw ρ (`neu t)     = {!!}
eval^Hw ρ (`seq t u)   = `seq (eval^Hw ρ t) (eval^Hw ρ u)
eval^Hw ρ `wir         = `wir
eval^Hw ρ `one         = `one
eval^Hw ρ `two         = `two
eval^Hw ρ (`ift b l r) with eval^Hw ρ b
... | `one = eval^Hw ρ l
... | `two = eval^Hw ρ r
... | v    = `ift v (eval^Hw ρ l) (eval^Hw ρ r)

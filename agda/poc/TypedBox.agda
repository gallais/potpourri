module poc.TypedBox where

open import Data.Empty
open import Agda.Builtin.Nat
open import Data.List.Base hiding ([_] ; _∷ʳ_)
open import Data.Product as P hiding (,_)
open import Relation.Nullary
open import Data.Sum
open import Function
open import Agda.Builtin.Equality as PEq using (_≡_)

data Ty :      Set
data Fo : Ty → Set

infixr 5 _`×_
data Ty where
  `Fin      : Nat → Ty
  _`×_ _`→_ : Ty → Ty → Ty
  C[_,_]    : {σ τ : Ty} → Fo σ → Fo τ → Ty

data Fo where
  instance
    `Fin : (n : Nat) → Fo (`Fin n)
    _`×_ : {σ τ : Ty} → Fo σ → Fo τ → Fo (σ `× τ)

oF : {σ : Ty} → Fo σ → Ty
oF {σ} _ = σ

data C : Ty → Set where
  C[_,_] : {s t : Ty} (σ : Fo s) (τ : Fo t) → C C[ σ , τ ]

Fo? : (σ : Ty) → Dec (Fo σ)
Fo? (`Fin k)   = yes (`Fin k)
Fo? (s `× t)   with Fo? s | Fo? t
... | yes p | yes q = yes (p `× q)
... | _ | _ = no whatever where postulate whatever : _ -- not interested in the negative cases
Fo? (s `→ t)   = no (λ ())
Fo? C[ s , t ] = no (λ ()) 

Fo?Fo! : {σ : Ty} (p : Fo σ) → Fo? σ ≡ yes p
Fo?Fo! (`Fin k) = PEq.refl
Fo?Fo! (p `× q) rewrite Fo?Fo! p | Fo?Fo! q = PEq.refl

C? : (σ : Ty) → Dec (C σ)
C? (`Fin k)   = no (λ ())
C? (s `× t)   = no (λ ())
C? (s `→ t)   = no (λ ())
C? C[ s , t ] = yes C[ s , t ]

⌞_⌟ : List Ty → List (∃ Fo)
⌞ []     ⌟ = []
⌞ σ ∷ Γ  ⌟ with Fo? σ
⌞ σ ∷ Γ ⌟ | yes p = (σ , p) ∷ ⌞ Γ ⌟
⌞ σ ∷ Γ ⌟ | no ¬p = ⌞ Γ ⌟

`X : List (∃ Fo) → ∃ Fo
`X []       = `Fin 1 , `Fin 1
`X (σ ∷ Γ)  = P.zip _`×_ _`×_ σ (`X Γ)

module _ {I : Set} where

  infixr 2 κ_
  κ_ : Set → (I → Set)
  (κ A) i = A

  infixr 3 _∙×_
  _∙×_ : (I → Set) → (I → Set) → (I → Set)
  (A ∙× B) i = A i × B i

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

module Term (𝓖 : {s t : Ty} (σ : Fo s) (τ : Fo t) → Set) where

  data Tm : Ty → List Ty → Set where
    `gat : {s t : Ty} {σ : Fo s} {τ : Fo t} →
           [ κ 𝓖 σ τ ∙→ Tm C[ σ , τ ] ]
    `box : {s t : Ty} {σ : Fo s} {τ : Fo t} →
           [ Tm (s `→ t) ∙→ Tm C[ σ , τ ] ]
    `run : {s t : Ty} {σ : Fo s} {τ : Fo t} →
           [ Tm C[ σ , τ ] ∙→ Tm (s `→ t) ]

    `var : {σ : Ty} → [ Var σ ∙→ Tm σ ]
    `lam : {σ τ : Ty} →
           [ (σ ∷_) ⊢ Tm τ ∙→ Tm (σ `→ τ) ]
    `app : {σ τ : Ty} →
           [ Tm (σ `→ τ) ∙→ Tm σ ∙→ Tm τ ]
    `fst : {σ τ : Ty} →
           [ Tm (σ `× τ) ∙→ Tm σ ]
    `snd : {σ τ : Ty} →
           [ Tm (σ `× τ) ∙→ Tm τ ]
    `prd : {σ τ : Ty} →
           [ Tm σ ∙→ Tm τ ∙→ Tm (σ `× τ) ]
    `zro : {n : Nat} →
           [ Tm (`Fin (suc n)) ]
    `suc : {n : Nat} →
           [ Tm (`Fin n) ∙→ Tm (`Fin (suc n)) ]
    `cas : {n : Nat} (σ : Ty) →
           [ Tm (`Fin (suc n)) ∙→ Tm σ ∙→ Tm (`Fin n `→ σ) ∙→ Tm σ ]
    `bm! : (σ : Ty) → [ Tm (`Fin 0) ∙→ Tm σ ]

  `swap : {s t : Ty} {σ : Fo s} {τ : Fo t} → [ Tm C[ σ `× τ , τ `× σ ] ]
  `swap = `box (`lam (`prd (`snd (`var z)) (`fst (`var z))))

  _>>_ : {s t u : Ty} {σ : Fo s} {τ : Fo t} {ν : Fo u} →
         [ Tm C[ σ , τ ] ] → [ Tm C[ τ , ν ] ] → [ Tm C[ σ , ν ] ]
  c₁ >> c₂ = `box (`lam (`app (`run c₂) (`app (`run c₁) (`var z))))

  `if : {σ : Ty} → [ Tm (`Fin 2) ] → [ Tm σ ] → [ Tm σ ] → [ Tm σ ]
  `if b l r = `cas _ b l (`lam r)


data Cover {A : Set} : List A → List A → List A → Set where
  []   : Cover [] [] []
  _∷_  : (a : A) {as bs cs : List A} →
         Cover as bs cs → Cover (a ∷ as) (a ∷ bs) (a ∷ cs)
  _∷ˡ_ : (a : A) {as bs cs : List A} →
         Cover as bs cs → Cover (a ∷ as) bs (a ∷ cs)
  _∷ʳ_ : (a : A) {as bs cs : List A} →
         Cover as bs cs → Cover as (a ∷ bs) (a ∷ cs)

left : {A : Set} {as : List A} → Cover as [] as
left {as = []}     = []
left {as = a ∷ as} = a ∷ˡ left

right : {A : Set} {as : List A} → Cover [] as as
right {as = []}     = []
right {as = a ∷ as} = a ∷ʳ right

data OPE {A : Set} : List A → List A → Set where
  []   : {as : List A} → OPE [] as
  _∷_  : (a : A) {as bs : List A} → OPE as bs → OPE (a ∷ as) (a ∷ bs)
  _∷ʳ_ : (a : A) {as bs : List A} → OPE as bs → OPE as (a ∷ bs)

refl : {A : Set} {as : List A} → OPE as as
refl {as = []}     = []
refl {as = a ∷ as} = a ∷ refl

trans : {A : Set} {as bs cs : List A} → OPE as bs → OPE bs cs → OPE as cs
trans []        p        = []
trans o         (a ∷ʳ p) = a ∷ʳ trans o p
trans (.a ∷ o)  (a ∷ p)  = a ∷ trans o p
trans (.a ∷ʳ o) (a ∷ p)  = a ∷ʳ trans o p

merge : {A : Set} {as bs cs : List A} → OPE as cs → OPE bs cs →
        ∃ λ ds → Cover as bs ds × OPE ds cs
merge []       q         = _ , right , q
merge p        []        = _ , left  , p
merge (a ∷ p)  (.a ∷ q)  = case merge p q of λ where (_ , c , o) → _ , a ∷ c  , a ∷ o
merge (a ∷ p)  (.a ∷ʳ q) = case merge p q of λ where (_ , c , o) → _ , a ∷ˡ c , a ∷ o
merge (a ∷ʳ p) (.a ∷ q)  = case merge p q of λ where (_ , c , o) → _ , a ∷ʳ c , a ∷ o
merge (a ∷ʳ p) (.a ∷ʳ q) = case merge p q of λ where (_ , c , o) → _ , c      , a ∷ʳ o


Thinnable : {A : Set} → (List A → Set) → Set
Thinnable T = [ T ∙→ □ OPE T ]

th^□ : {A : Set} {T : List A → Set} → Thinnable (□ OPE T)
th^□ t o p = t (trans o p)


module Normal (𝓖 : {s t : Ty} (σ : Fo s) (τ : Fo t) → Set) where

  data Neu : Ty → Set where
    instance
      `Fin    : (n : Nat) → Neu (`Fin n)
      C[_,_]  : {s t : Ty} (σ : Fo s) (τ : Fo t) → Neu (C[ σ , τ ])

  data Ne  : Ty → List Ty → Set
  data Nf  : Ty → List Ty → Set
  data Abs : Ty → Ty → List Ty → Set
  data Hdw : {s t : Ty} → Fo s → Fo t → List Ty → Set

  data Ne where
    `var : {σ : Ty} → Ne σ (σ ∷ [])
    `run : {s t : Ty} {σ : Fo s} {τ : Fo t} → [ Ne C[ σ , τ ] ∙→ Ne (s `→ t) ]

    `app : {σ τ : Ty} {Γ Δ Γ⋈Δ : List Ty} →
           Ne (σ `→ τ) Γ → Nf σ Δ → Cover Γ Δ Γ⋈Δ → Ne τ Γ⋈Δ
    `fst : {σ τ : Ty} →
           [ Ne (σ `× τ) ∙→ Ne σ ]
    `snd : {σ τ : Ty} →
           [ Ne (σ `× τ) ∙→ Ne τ ]
    `cas : {n : Nat} {σ : Ty} {Γ Δ Γ⋈Δ Θ Γ⋈Δ⋈Θ : List Ty} →
           Ne (`Fin (suc n)) Γ → Nf σ Δ → Nf (`Fin n `→ σ) Θ →
           Cover Γ Δ Γ⋈Δ → Cover Γ⋈Δ Θ Γ⋈Δ⋈Θ → Ne σ Γ⋈Δ⋈Θ
    `bm! : (σ : Ty) → [ Ne (`Fin 0) ∙→ Ne σ ]
    `box : {s t : Ty} {σ : Fo s} {τ : Fo t} →
           [ Ne (s `→ t) ∙→ Ne C[ σ , τ ] ]

  data Nf where

    `lam : {σ τ : Ty} → [ Abs σ τ ∙→ Nf (σ `→ τ) ]
    `prd : {σ τ : Ty} {Γ Δ Γ⋈Δ : List Ty} →
           Nf σ Γ → Nf τ Δ → Cover Γ Δ Γ⋈Δ → Nf (σ `× τ) Γ⋈Δ
    `zro : {n : Nat} → Nf (`Fin (suc n)) []
    `suc : {n : Nat} → [ Nf (`Fin n) ∙→ Nf (`Fin (suc n)) ]
    `cct : {s t : Ty} → {σ : Fo s} {τ : Fo t} →
           [ Hdw σ τ ∙→ Nf C[ σ , τ ] ]
    `neu : {σ : Ty} {{_ : Neu σ}} → [ Ne σ ∙→ Nf σ ]


  data Abs where
    `cst : {σ τ : Ty} → [ Nf τ           ∙→ Abs σ τ ]
    `bnd : {σ τ : Ty} → [ (σ ∷_) ⊢ Nf τ  ∙→ Abs σ τ ]


  data Hdw where
    `gat : {s t : Ty} {σ : Fo s} {τ : Fo t} →
           [ κ 𝓖 σ τ ∙→ Hdw σ τ ]
    `seq : {s t u : Ty} {σ : Fo s} {τ : Fo t} {ν : Fo u} →
           [ Hdw σ τ ∙→ Hdw τ ν ∙→ Hdw σ ν ]
    `par : {s t u v : Ty} {σ : Fo s} {τ : Fo t} {ν : Fo u} {ω : Fo v} →
           [ Hdw σ τ ∙→ Hdw ν ω ∙→ Hdw (σ `× ν) (τ `× ω) ]

    -- captured
    `neu : {s t : Ty} {σ : Fo s} {τ : Fo t} → [ Ne C[ σ , τ ]  ∙→ Hdw σ τ ]
    `box : {s t : Ty} {σ : Fo s} {τ : Fo t} → [ Nf (s `→ t)    ∙→ Hdw σ τ ]

    -- structural
    `swp : {s t : Ty} {σ : Fo s} {τ : Fo t} → [ Hdw (σ `× τ) (τ `× σ) ]
    `asr : {s t u : Ty} {σ : Fo s} {τ : Fo t} {ν : Fo u} →
           [ Hdw ((σ `× τ) `× ν) (σ `× τ `× ν) ]
    `asl : {s t u : Ty} {σ : Fo s} {τ : Fo t} {ν : Fo u} →
           [ Hdw (σ `× τ `× ν) ((σ `× τ) `× ν) ]

    -- basic gates
    `wir : {s : Ty} {σ : Fo s}              → [ Hdw σ σ ]
    `zro : {n : Nat}                        → [ Hdw (`Fin 1) (`Fin (suc n)) ]
    `suc : {n : Nat}                        → [ Hdw (`Fin n) (`Fin (suc n)) ]
    `dbl : {s : Ty} {σ : Fo s}              → [ Hdw σ (σ `× σ) ]
    `pi1 : {s t : Ty} {σ : Fo s} {τ : Fo t} → [ Hdw (σ `× τ) σ ]
    `pi2 : {s t : Ty} {σ : Fo s} {τ : Fo t} → [ Hdw (σ `× τ) τ ]

record Emb {A : Set} (E : List A → Set) (Δ : List A) : Set where
  constructor `emb
  field {context} : List A
        value     : E context
        ope       : OPE context Δ

map^Emb : {A : Set} {E F : List A → Set} → [ E ∙→ F ] → [ Emb E ∙→ Emb F ]
map^Emb f (`emb e pr) = `emb (f e) pr

join^Emb : {A : Set} {E : List A → Set} → [ Emb (Emb E) ∙→ Emb E ]
join^Emb (`emb (`emb e ope₂) ope₁) = `emb e (trans ope₂ ope₁)

th^Emb : {A : Set} {E : List A → Set} → Thinnable (Emb E)
th^Emb (`emb v ope) ρ = `emb v (trans ope ρ)

infix 1 _─Env
record _─Env {A : Set} (Γ : List A) (𝓥 : A → List A → Set) (Δ : List A) : Set where
  constructor pack
  field lookup : {a : A} → Var a Γ → 𝓥 a Δ
open _─Env

ε : {A : Set} {𝓥 : A → List A → Set} {Δ : List A} → ([] ─Env) 𝓥 Δ
lookup ε ()

_∙_ : {A : Set} {Γ Δ : List A} {𝓥 : A → List A → Set} {a : A} →
      (Γ ─Env) 𝓥 Δ → 𝓥 a Δ → (a ∷ Γ ─Env) 𝓥 Δ
lookup (ρ ∙ v) z     = v
lookup (ρ ∙ v) (s k) = lookup ρ k

th^Env : {A : Set} {𝓥 : A → List A → Set} {Γ : List A} →
         ((a : A) → Thinnable (𝓥 a)) → Thinnable ((Γ ─Env) 𝓥)
lookup (th^Env th^𝓥 ρ o) k = th^𝓥 _ (lookup ρ k) o

module Model (𝓖 : {s t : Ty} (σ : Fo s) (τ : Fo t) → Set) where

  open Term   𝓖
  open Normal 𝓖


  _─Comp : (Γ : List Ty) (𝓥 : Ty → List Ty → Set) (Δ : List Ty) → Set
  (Γ ─Comp) 𝓒 Δ = {σ : Ty} → Tm σ Γ → 𝓒 σ Δ

  Mod : Ty → List Ty → Set
  Mod (`Fin n)             = Emb (Nf (`Fin n))
  Mod (σ `× τ)             = Mod σ ∙× Mod τ
  Mod (σ `→ τ)             = □ OPE (Mod σ ∙→ Mod τ)
  Mod (C[_,_] {a} {b} σ τ) = Emb (Hdw σ τ) ∙× □ OPE (Mod a ∙→ Mod b)

  th^Mod : (σ : Ty) → Thinnable (Mod σ)
  th^Mod (`Fin n)   t       ope = th^Emb t ope
  th^Mod (σ `× τ)   (p , q) ope = th^Mod σ p ope , th^Mod τ q ope
  th^Mod (σ `→ τ)   f       ope = th^□ f ope
  th^Mod C[ σ , τ ] (c , f) ope = th^Emb c ope , th^□ f ope

  -- As usual: the model is defined so that it is possible
  -- to both extract normal forms from it and embed neutral
  -- forms into it
  reify   : (σ : Ty) → [ Mod σ      ∙→ Emb (Nf σ) ]
  reflect : (σ : Ty) → [ Emb (Ne σ) ∙→ Mod σ      ]

  -- reify
  reify (`Fin n) v = v

  reify (σ `× τ) (p , q)
    with reify σ p | reify τ q
  ... | `emb t pr | `emb u pr'
    with merge pr pr'
  ... | _ , cover , ope = `emb (`prd t u cover) ope

  reify (σ `→ τ) f
    with reify τ (f (σ ∷ʳ refl) (reflect σ (`emb `var (σ ∷ []))))
  ... | `emb b (.σ ∷ pr)  = `emb (`lam (`bnd b)) pr
  ... | `emb b []         = `emb (`lam (`cst b)) []
  ... | `emb b (.σ ∷ʳ pr) = `emb (`lam (`cst b)) pr

  reify C[ σ , τ ] = map^Emb `cct ∘ proj₁

  -- reflect
  reflect (`Fin n)   t = map^Emb `neu t
  reflect (σ `× τ)   p = reflect σ (map^Emb `fst p) , reflect τ (map^Emb `snd p)
  reflect (σ `→ τ)   f = λ ope v →
                         let (`emb t pr)       = f
                             (`emb u pr')      = reify σ v
                             (_ , cover , ope) = merge (trans pr ope) pr'
                         in reflect τ (`emb (`app t u cover) ope)

  reflect (C[_,_] {a} {b} σ τ) c = map^Emb `neu c
                       , λ ope v →
                         let (`emb t pr)       = c
                             (`emb u pr')      = reify a v
                             (_ , cover , ope) = merge (trans pr ope) pr'
                         in reflect b (`emb (`app (`run t) u cover) ope)

  fresh : (σ : Ty) → [ (σ ∷_) ⊢ Mod σ ]
  fresh σ = reflect σ (`emb `var (σ ∷ []))

  eval : {Γ Δ : List Ty} → (Γ ─Env) Mod Δ → (Γ ─Comp) Mod Δ
  eval ρ (`gat g)     = `emb (`gat g) [] , {!!}
  eval ρ (`box t)     = map^Emb `box (reify (_ `→ _) (eval ρ t)) , eval ρ t
  eval ρ (`run t)     = proj₂ (eval ρ t)
  eval ρ (`var v)     = lookup ρ v
  eval ρ (`lam b)     = λ ope v → eval (th^Env th^Mod ρ ope ∙ v) b
  eval ρ (`app t u)   = eval ρ t refl (eval ρ u) 
  eval ρ (`fst t)     = proj₁ (eval ρ t)
  eval ρ (`snd t)     = proj₂ (eval ρ t)
  eval ρ (`prd t u)   = eval ρ t , eval ρ u
  eval ρ `zro         = `emb `zro []
  eval ρ (`suc t)     = map^Emb `suc (eval ρ t)
  eval ρ (`cas σ t l r) with eval ρ t
  ... | `emb `zro      pr = eval ρ l
  ... | `emb (`suc v)  pr = eval ρ r refl (`emb v pr)
  ... | `emb (`neu ne) pr
    with reify σ (eval ρ l) | reify (`Fin _ `→ σ) (eval ρ r)
  ... | `emb lnf prl | `emb rnf prr
    with merge pr prl
  ... | _ , pr⋈prl , ope
    with merge ope prr
  ... | _ , ope⋈prr , ope' = reflect σ (`emb (`cas ne lnf rnf pr⋈prl ope⋈prr) ope')
  eval ρ (`bm! σ t) with eval ρ t
  ... | `emb (`neu ne) pr = reflect σ (`emb (`bm! σ ne) pr)


  data Cct : {s t : Ty} → Fo s → Fo t → Set where
    -- cf code commented out for ideas

  cct : {s t : Ty} {σ : Fo s} {τ : Fo t} → Nf C[ σ , τ ] [] → Cct σ τ
  cct = {!!}

  specialise : {s t : Ty} {σ : Fo s} {τ : Fo t} → Tm C[ σ , τ ] [] → Cct σ τ
  specialise t with reify C[ _ , _ ] {[]} (eval ε t)
  ... | `emb nf [] = cct nf


{-
  dispatch : {Γ Δ Θ : List Ty} → Cover Γ Δ Θ →
             [ Hdw (proj₂ (`X ⌞ Θ ⌟)) (proj₂ (`X ⌞ Γ ⌟) `× proj₂ (`X ⌞ Δ ⌟)) ]
  dispatch []       = `dbl
  dispatch (σ ∷ Γ)  with Fo? σ
  ... | yes p = `seq (`par `dbl (dispatch Γ))
              $ `seq `asl
              $ `seq (`par (`seq `asr `swp) `wir)
              $ `asr
  ... | no ¬p = dispatch Γ
  dispatch (σ ∷ˡ Γ) with Fo? σ
  ... | yes p = `seq (`par `wir (dispatch Γ)) `asl
  ... | no ¬p = dispatch Γ
  dispatch (σ ∷ʳ Γ) with Fo? σ
  ... | yes p = `seq (`par `wir (dispatch Γ)) $ `seq `asl $ `seq (`par `swp `wir) `asr
  ... | no ¬p = dispatch Γ


  cct  : {s t : Ty} (σ : Fo s) (τ : Fo t) → [ Nf (s `→ t) ∙→ Cct σ τ ]
  cct' : {s : Ty} (σ : Fo s) {Γ : List Ty} → Nf s Γ → Hdw (proj₂ (`X ⌞ Γ ⌟)) σ Γ

  cct _ τ (`lam (`cst t)) = `seq `pi2 (cct' τ t)
  cct {a} σ τ (`lam (`bnd b)) with Fo? a | Fo?Fo! σ | cct' τ b
  ... | yes p | PEq.refl | v = v
  ... | no ¬p | ()       | _

  cct' (σ `× τ)        (`prd a b split) = `seq (dispatch split) (`par (cct' σ a) (cct' τ b))
  cct' (`Fin (suc n))  `zro             = `zro
  cct' (`Fin (suc n))  (`suc k)         = `seq (cct' (`Fin n) k) `suc
  cct' τ               (`neu ne)        = {!!}
-}

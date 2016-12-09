module models.models where

open import Size
open import Data.Nat
open import Data.Fin
open import Data.Empty
open import Data.Unit
open import Data.Vec     as V hiding ([_])
open import Data.Sum     as S
open import Data.Product as P
open import Function

infixr 10 _`→_
infixr 11 _`×_
infixr 12 _`+_

data Desc : Size → Set
data Type : Size → Set

data Desc where
  `x   : ∀ {i} → Desc i
  `κ   : ∀ {i} → Type i → Desc i
  _`+_ : ∀ {i} → Desc i  → Desc i  → Desc i 
  _`×_ : ∀ {i} → Desc i  → Desc i  → Desc i
  _`→_ : ∀ {i} → Type i → Desc i → Desc i

data Type where
  `1   : ∀ {i} → Type i
  _`+_ : ∀ {i} → Type i → Type i → Type i
  _`×_ : ∀ {i} → Type i → Type i → Type i
  _`→_ : ∀ {i} → Type i → Type i → Type i
  `μ   : ∀ {i} → Desc i → Type (↑ i)

module ⟦Desc⟧ {i} (⟦_⟧ : Type i → Set) where

  ⟦_⟧d : Desc i → Set → Set
  ⟦ `x     ⟧d X = X
  ⟦ `κ σ   ⟧d X = ⟦ σ ⟧
  ⟦ d `+ e ⟧d X = ⟦ d ⟧d X ⊎ ⟦ e ⟧d X
  ⟦ d `× e ⟧d X = ⟦ d ⟧d X × ⟦ e ⟧d X
  ⟦ σ `→ d ⟧d X = ⟦ σ ⟧ → ⟦ d ⟧d X

  data μ (d : Desc i) : Set where
    ⟨_⟩ : ⟦ d ⟧d (μ d) → μ d

open ⟦Desc⟧

`Type = Type ∞

⟦_⟧ : ∀ {i} → Type i → Set
⟦ `1      ⟧ = ⊤
⟦ σ `+  τ ⟧ = ⟦ σ ⟧ ⊎ ⟦ τ ⟧
⟦ σ `×  τ ⟧ = ⟦ σ ⟧ × ⟦ τ ⟧
⟦ σ `→ τ  ⟧ = ⟦ σ ⟧ → ⟦ τ ⟧
⟦ `μ d    ⟧ = μ ⟦_⟧ d

`⟦_⟧ : ∀ {i} → Desc i → Type i → Type i
`⟦ `x     ⟧ X = X
`⟦ `κ v   ⟧ X = v
`⟦ d `+ e ⟧ X = `⟦ d ⟧ X `+ `⟦ e ⟧ X
`⟦ d `× e ⟧ X = `⟦ d ⟧ X `× `⟦ e ⟧ X
`⟦ v `→ d ⟧ X = v `→ `⟦ d ⟧ X

`ℕ : `Type
`ℕ = `μ (`κ `1 `+ `x)

`List : `Type → `Type
`List σ = `μ (`κ `1 `+ (`κ σ `× `x))

`BTree : `Type → `Type → `Type
`BTree n l = `μ (`κ l `+ (`x `× `κ n `× `x))

`0 : ⟦ `ℕ ⟧
`0 = ⟨ inj₁ _ ⟩

`3 : ⟦ `ℕ ⟧
`3 = ⟨ inj₂ ⟨ inj₂ ⟨ inj₂ `0 ⟩ ⟩ ⟩

`0∷3 : ⟦ `List `ℕ ⟧
`0∷3 = ⟨ inj₂ (`0 , ⟨ inj₂ (`3 , ⟨ inj₁ _ ⟩) ⟩) ⟩

`btree : ⟦ `BTree (`List `ℕ) `ℕ ⟧
`btree = ⟨ (inj₂ (⟨ inj₁ `0 ⟩
                 , `0∷3
                 , ⟨ inj₁ `3 ⟩)) ⟩

open import Data.List as L hiding ([_])

Model : Set₁
Model = ∀ {i} → Type i → List `Type → Set

module _ {I : Set} where

  infixr 10 _⟶_
  infixr 11 _∙×_
  infixr 12 _∙⊎_

  _⟶_ : (X Y : I → Set) → I → Set
  (X ⟶ Y) i = X i → Y i

  _∙⊎_ : (X Y : I → Set) → I → Set
  (X ∙⊎ Y) i = X i ⊎ Y i

  _∙×_ : (X Y : I → Set) → I → Set
  (X ∙× Y) i = X i × Y i

  [_] : (I → Set) → Set
  [ T ] = ∀ {i} → T i

module _ {I : Set} where

  infixr 13 _⊢_
  _⊢_ : I → (List I → Set) → (List I → Set)
  (σ ⊢ T) Γ = T (σ ∷ Γ)

  data Var : I → List I → Set where
    ze : ∀ {σ}   → [ σ ⊢ Var σ ]
    su : ∀ {σ τ} → [ Var σ ⟶ τ ⊢ Var σ ]

  record _─Env (Γ : List I) (V : I → List I → Set) (Δ : List I) : Set where
    constructor pack
    field get : ∀ {σ} → Var σ Γ → V σ Δ
  open _─Env public

  ε : ∀ {V Δ} → ([] ─Env) V Δ
  ε = pack λ ()

  _∙_ : ∀ {Γ σ V Δ} → (Γ ─Env) V Δ → V σ Δ → ((σ ∷ Γ) ─Env) V Δ
  get (ρ ∙ v) ze     = v
  get (ρ ∙ v) (su k) = get ρ k

  _⊆_ : List I → List I → Set
  Γ ⊆ Δ = (Γ ─Env) Var Δ

  Thinning : (List I → Set) → Set
  Thinning T = ∀ {Γ Δ} → Γ ⊆ Δ → T Γ → T Δ

  thEnv : ∀ {Γ V} → (∀ {i} → Thinning (V i)) → Thinning ((Γ ─Env) V)
  get (thEnv th ρ vs) k = th ρ (get vs k)

  refl : ∀ {Γ} → Γ ⊆ Γ
  refl = pack id

  trans : ∀ {Γ Δ Θ V} → Γ ⊆ Δ → (Δ ─Env) V Θ → (Γ ─Env) V Θ
  get (trans ρ σ) k = get σ (get ρ k)

  extend : ∀ {Γ i} → Γ ⊆ (i ∷ Γ)
  extend = pack su

  copy : ∀ {Γ Δ i} → Γ ⊆ Δ → (i ∷ Γ) ⊆ (i ∷ Δ)
  copy ρ = trans ρ extend ∙ ze

  □ : (List I → Set) → (List I → Set)
  (□ T) Γ = ∀ {Δ} → Γ ⊆ Δ → T Δ

  th□ : ∀ {T} → Thinning (□ T)
  th□ ρ t = t ∘ trans ρ

record Mode : Set₁ where
  field
    EMB : `Type → Set
    CUT : `Type → Set

module Calculus {{m : Mode}} where

  open Mode m

  mutual

    data Nf : Model where
      `λ   : ∀ {σ τ} →         [ σ ⊢ Nf τ           ⟶ Nf (σ `→ τ) ]
      `ne  : ∀ {σ}   → EMB σ → [ Ne σ               ⟶ Nf σ        ]
      `tt  :                   [                      Nf `1       ]
      `inl : ∀ {σ τ} →         [ Nf σ               ⟶ Nf (σ `+ τ) ]
      `inr : ∀ {σ τ} →         [ Nf τ               ⟶ Nf (σ `+ τ) ]
      _`,_ : ∀ {σ τ} →         [ Nf σ ⟶ Nf τ        ⟶ Nf (σ `× τ) ]
      `⟨_⟩ : ∀ {d}   →         [ Nf (`⟦ d ⟧ (`μ d)) ⟶ Nf (`μ d)   ]

    data Ne : Model where
      -- heads
      `var : ∀ {σ}     →         [ Var σ                                    ⟶ Ne σ ]
      `cut : ∀ {σ}     → CUT σ → [ Nf σ                                     ⟶ Ne σ ]
      -- spines
      _`$_ : ∀ {σ τ}   →         [ Ne (σ `→ τ) ⟶ Nf σ                       ⟶ Ne τ ]
      `fst : ∀ {σ τ}   →         [ Ne (σ `× τ)                              ⟶ Ne σ ]
      `snd : ∀ {σ τ}   →         [ Ne (σ `× τ)                              ⟶ Ne τ ]
      `cse : ∀ {σ τ ν} →         [ Ne (σ `+ τ) ⟶ Nf (σ `→ ν) ⟶ Nf (τ `→ ν)  ⟶ Ne ν ]
      `rec : ∀ {d σ}   →         [ Nf (`⟦ d ⟧ (`μ d `× σ) `→ σ) ⟶ Ne (`μ d) ⟶ Ne σ ]



  thNf : ∀ {i} {σ : Type i} → Thinning (Nf σ)
  thNe : ∀ {i} {σ : Type i} → Thinning (Ne σ)

  thNf ρ (`λ b)    = `λ (thNf (copy ρ) b)
  thNf ρ (`ne p t) = `ne p (thNe ρ t)
  thNf ρ `tt       = `tt
  thNf ρ (`inl t)  = `inl (thNf ρ t)
  thNf ρ (`inr t)  = `inr (thNf ρ t)
  thNf ρ (t `, u)  = thNf ρ t `, thNf ρ u
  thNf ρ `⟨ t ⟩    = `⟨ thNf ρ t ⟩

  thNe ρ (`var k)     = `var (get ρ k)
  thNe ρ (`cut p t)   = `cut p (thNf ρ t)
  thNe ρ (f `$ t)     = thNe ρ f `$ thNf ρ t
  thNe ρ (`fst t)     = `fst (thNe ρ t)
  thNe ρ (`snd t)     = `snd (thNe ρ t)
  thNe ρ (`cse t l r) = `cse (thNe ρ t) (thNf ρ l) (thNf ρ r)
  thNe ρ (`rec alg t) = `rec (thNf ρ alg) (thNe ρ t)


open Calculus

instance

  Raw : Mode
  Mode.EMB Raw = const ⊤
  Mode.CUT Raw = const ⊤

Infer = Calculus.Ne {{Raw}}
Check = Calculus.Nf {{Raw}}

`zero : [ Check `ℕ ]
`zero = `⟨ `inl `tt ⟩

`succ : [ Check (`ℕ `→ `ℕ) ]
`succ = `λ `⟨ `inr (`ne _ (`var ze)) ⟩

`two : [ Check `ℕ ]
`two = `ne _ (`cut _ `succ `$ `ne _ (`cut _ `succ `$ `zero))

`id : {σ : `Type} → [ Check (σ `→ σ) ]
`id = `λ (`ne _ (`var ze))

`plus : [ Check (`ℕ `→ `ℕ `→ `ℕ) ]
`plus = `λ (`λ (`ne _
       (`rec (`λ (`ne _ (`cse (`var ze)
                              (`λ (`ne _ (`var (su (su ze)))))
                              (`λ (`ne _ (`cut _ `succ `$ `ne _ (`snd (`var ze))))))))
             (`var (su ze)))))
             

instance

  βηι : Mode
  Mode.EMB βηι = λ { (_ `+ _) → ⊤
                   ; (`μ _)   → ⊤
                   ; _        → ⊥ }
  Mode.CUT βηι = const ⊥

  βι : Mode
  Mode.EMB βι = const ⊤
  Mode.CUT βι = const ⊥

Neut = Calculus.Ne {{βηι}}
Norm = Calculus.Nf {{βηι}}

module ValDesc {i} (Val : Type i → List `Type → Set) where

  ValD : (d : Desc i) (x : Type i) → (List `Type → Set) → (List `Type → Set)
  ValD `x       x X Γ = X Γ
  ValD (`κ σ)   x X Γ = Val σ Γ
  ValD (d `+ e) x X Γ = Neut (`⟦ d `+ e ⟧ x) Γ ⊎ ValD d x X Γ ⊎ ValD e x X Γ
  ValD (d `× e) x X Γ = ValD d x X Γ × ValD e x X Γ
  ValD (σ `→ d) x X = □ (Val σ ⟶ ValD d x X)

  data Valμ (d : Desc i) (Γ : List `Type) : Set where
    `ne  : Neut (`μ d) Γ  → Valμ d Γ
    `⟨_⟩ : ValD d {!`μ d!} (Valμ d) Γ → Valμ d Γ -- aren't we supposed to have subtyping?!
open ValDesc

Val : Model
Val `1        Γ = ⊤
Val (σ `+ τ)  Γ = Neut (σ `+ τ) Γ ⊎ Val σ Γ ⊎ Val τ Γ
Val (σ `× τ)  Γ = Val σ Γ × Val τ Γ
Val (σ `→ τ)  Γ = □ (Val σ ⟶ Val τ) Γ
Val (`μ d)      = Valμ Val d

thVal : ∀ {i} (σ : Type i) → Thinning (Val σ)
thVal `1        ρ = id
thVal (σ `+ τ)  ρ = S.map (thNe ρ) $ S.map (thVal σ ρ) (thVal τ ρ)
thVal (σ `× τ)  ρ = P.map (thVal σ ρ) (thVal τ ρ)
thVal (σ `→ τ)  ρ = th□ ρ
thVal (`μ d)    ρ = {!!}


{-
SUCC : [ Val (`ℕ `→ `ℕ) ]
SUCC = λ inc v → `⟨ inj₂ (inj₂ v) ⟩

reify   : ∀ σ → [ Val σ  ⟶ Norm σ  ]
reflect : ∀ σ → [ Neut σ ⟶ Val σ   ]

reify   `1        = const `tt
reify   (σ `+ τ)  = S.[ `ne _ , S.[ `inl ∘ reify σ  , `inr ∘ reify τ ] ]
reify   (σ `× τ)  = uncurry _`,_ ∘ P.map (reify σ) (reify τ)
reify   (σ `→ τ)  = λ b → `λ (reify τ (b extend (reflect σ (`var ze))))
reify   (`μ d)    = {!!}

reflect `1        t = tt
reflect (σ `+ τ)  t = inj₁ t
reflect (σ `× τ)  t = reflect σ (`fst t) , reflect τ (`snd t)
reflect (σ `→ τ)  t = λ ρ v → reflect τ (thNe ρ t `$ reify σ v)
reflect (`μ d)    t = {!!}

{-
CASE : ∀ {σ τ ν} → [ Val (σ `+ τ) ⟶ Val (σ `→ ν) ⟶ Val (τ `→ ν) ⟶ Val ν ]
CASE {σ} {τ} {ν} t l r =
  S.[ (λ ne → reflect ν (`cse ne (reify (σ `→ ν) l) (reify (τ `→ ν) r)))
    , S.[ l refl , r refl ] 
    ] t


REC    : ∀ {σ n Γ} {d : Desc Type n ∞} {ps : Vec `Type n} →
         Val (`⟦ d ⟧ ps (`μ d ps `× σ) `→ σ) Γ →
         μ⟦ Val ⟧ d ps Γ → Val σ Γ
REC<$> : ∀ {σ n Γ} (d d′ : Desc Type n ∞) {ps : Vec `Type n} →
         Val (`⟦ d′ ⟧ ps (`μ d′ ps `× σ) `→ σ) Γ →
         Val⟦ d ⟧ Val ps (μ⟦ Val ⟧ d′ ps) Γ → Val (`⟦ d ⟧ ps (`μ d′ ps `× σ)) Γ


REC {σ}     alg (`ne t) = reflect _ (`rec (reify (_ `→ σ) alg) t)
REC {d = d} alg `⟨ t ⟩  = alg refl (REC<$> d d alg t)

REC<$> (`v k)   d′ alg t        = t
REC<$> `x       d′ alg t        = t , REC alg t
REC<$> (`κ v)   d′ alg t        = t
REC<$> (d `+ e) d′ alg (inj₁ t) = inj₂ (inj₁ (REC<$> d d′ alg t))
REC<$> (d `+ e) d′ alg (inj₂ t) = inj₂ (inj₂ (REC<$> e d′ alg t))
REC<$> (d `× e) d′ alg (t , u)  = REC<$> d d′ alg t , REC<$> e d′ alg u
REC<$> (v `→ d) d′ alg t        = λ σ v → REC<$> d d′ (alg ∘ trans σ) (t σ v)

DATA  : ∀ {Γ n} (d d′ : Desc Type n ∞) {ps : Vec `Type n} →
        Val (`⟦ d ⟧ ps (`μ d′ ps)) Γ → Val⟦ d ⟧ Val ps (μ⟦ Val ⟧ d′ ps) Γ
DATA (`v k)   d′ t        = t
DATA `x       d′ t        = t
DATA (`κ v)   d′ t        = t
DATA (d `+ e) d′ (inj₁ x) = {!!}
DATA (d `+ e) d′ (inj₂ t) = inj₂ (S.map (DATA d d′) (DATA e d′) t)
DATA (d `× e) d′ (t , u)  = DATA d d′ t , DATA e d′ u
DATA (v `→ d) d′ t        = λ ρ v → DATA d d′ (t ρ v)


evalCheck : ∀ {Γ Δ σ} → (Γ ─Env) Val Δ → Check σ Γ → Val σ Δ
evalInfer : ∀ {Γ Δ σ} → (Γ ─Env) Val Δ → Infer σ Γ → Val σ Δ

evalCheck ρ (`λ b)    = λ σ v → evalCheck (thEnv (thVal _) σ ρ ∙ v) b
evalCheck ρ (`ne _ t) = evalInfer ρ t
evalCheck ρ `tt       = tt
evalCheck ρ (`inl t)  = inj₂ (inj₁ (evalCheck ρ t))
evalCheck ρ (`inr t)  = inj₂ (inj₂ (evalCheck ρ t))
evalCheck ρ (t `, u)  = evalCheck ρ t , evalCheck ρ u
evalCheck {σ = `μ d ps} ρ `⟨ t ⟩ = `⟨ DATA d d (evalCheck ρ t) ⟩

evalInfer ρ (`var k)     = get ρ k
evalInfer ρ (`cut _ t)   = evalCheck ρ t
evalInfer ρ (f `$ t)     = evalInfer ρ f refl (evalCheck ρ t)
evalInfer ρ (`fst t)     = proj₁ (evalInfer ρ t)
evalInfer ρ (`snd t)     = proj₂ (evalInfer ρ t)
evalInfer ρ (`cse t l r) = CASE (evalInfer ρ t) (evalCheck ρ l) (evalCheck ρ r)
evalInfer ρ (`rec alg t) = REC (evalCheck ρ alg) (evalInfer ρ t) 
-}
-}

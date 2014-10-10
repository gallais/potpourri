module lib.Context where

import Data.Nat as ℕ
open import Data.Empty
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

{- definition of a context and context inclusion -}

module Context where

  infixl 20 _∙_
  data Con (A : Set) : Set where
    ε : Con A
    _∙_ : (Γ : Con A) (σ : A) → Con A

  length : ∀ {A} (γ : Con A) → ℕ.ℕ
  length ε       = 0
  length (γ ∙ σ) = 1 ℕ.+ length γ

  module Context where

    map : {A B : Set} (f : A → B) (Γ : Con A) → Con B
    map f ε       = ε
    map f (Γ ∙ σ) = map f Γ ∙ f σ

    infixl 5 _++_
    _++_ : {A : Set} (xs ys : Con A) → Con A
    xs ++ ε      = xs
    xs ++ ys ∙ σ = (xs ++ ys) ∙ σ

    induction : ∀ {A : Set} {P : Con A → Set}
                (c : (a : A) {γ : Con A} → P γ → P $ γ ∙ a) (n : P ε)
                (γ : Con A) → P γ
    induction c n ε       = n
    induction c n (γ ∙ σ) = c σ $ induction c n γ

    foldl : ∀ {A B : Set} (c : A → B → B) (n : B) (Γ : Con A) → B
    foldl {B = B} c = induction {P = λ _ → B} (λ a → c a)

    foldr : ∀ {A B : Set} (c : A → B → B) (n : B) (Γ : Con A) → B
    foldr c n ε       = n
    foldr c n (Γ ∙ σ) = foldr c (c σ n) Γ

    return : {A : Set} (a : A) → Con A
    return a = ε ∙ a

    subst : {A B : Set} (Γ : Con A) (f : A → Con B) → Con B
    subst Γ f = foldl (_++_ ∘ f) ε Γ
    syntax subst ma f = ma >>= f

    -- properties
    ε++ : {A : Set} (ys : Con A) → ε ++ ys ≡ ys
    ε++ ε        = Eq.refl
    ε++ (ys ∙ σ) = Eq.cong (flip _∙_ σ) $ ε++ ys

    map++ : ∀ {A B : Set} (f : A → B) (xs ys : Con A) →
            map f (xs ++ ys) ≡ map f xs ++ map f ys
    map++ f xs ε        = Eq.refl
    map++ f xs (ys ∙ σ) = Eq.cong (flip _∙_ (f σ)) $ map++ f xs ys

    assoc++ : ∀ {A : Set} (xs ys zs : Con A) →
              xs ++ ys ++ zs ≡ xs ++ (ys ++ zs)
    assoc++ xs ys ε        = Eq.refl
    assoc++ xs ys (zs ∙ σ) = Eq.cong (flip _∙_ σ) $ assoc++ xs ys zs 

  module Pointwise where

    data PCon {ℓ} {A : Set} (P : A → Set ℓ) : (γ : Con A) → Set ℓ where
      ε   : PCon P ε
      _∙_ : ∀ {γ σ} (Γ : PCon P γ) (S : P σ) → PCon P $ γ ∙ σ

    module Pointwise where

      pointwise : ∀ {A P} (prP : (a : A) → P a) (γ : Con A) → PCon P γ
      pointwise prP = Context.induction (λ a ih → ih ∙ prP a) ε

      map : ∀ {ℓ ℓ′} {A B} {P : A → Set ℓ} {Q : B → Set ℓ′} (f : A → B)
            (Pf : {a : A} → P a → Q $ f a)
            {γ : Con A} (Γ : PCon P γ) → PCon Q $ Context.map f γ
      map f Pf ε       = ε
      map f Pf (Γ ∙ S) = map f Pf Γ ∙ Pf S

      induction : ∀ {ℓ} {A} {P : A → Set ℓ} (Q : (γ : Con A) (Γ : PCon P γ) → Set ℓ)
                  (c : {a : A} (prP : P a) {γ : Con A} {Γ : PCon P γ}
                       (prQ : Q γ Γ) → Q (γ ∙ a) $ Γ ∙ prP)
                  (n : Q ε ε)
                  {γ : Con A} (Γ : PCon P γ) → Q γ Γ
      induction Q c n ε       = n
      induction Q c n (Γ ∙ S) = c S $ induction Q c n Γ

      foldl : ∀ {A} {P : A → Set} {B : Set} (c : (a : A) (b : B) → B) (n : B)
                  {γ : Con A} (Γ : PCon P γ) → B
      foldl {B = B} c n = induction (λ _ _ → B) (λ {a} _ → c a) n

      infixl 5 _++_
      _++_ : ∀ {ℓ} {A : Set} {P : A → Set ℓ} {xs ys : Con A}
             (XS : PCon P xs) (YS : PCon P ys) →
             PCon P $ xs Context.++ ys
      xs ++ ε      = xs
      xs ++ ys ∙ σ = (xs ++ ys) ∙ σ

module Inclusion where

  open Context

  data _⊆_ {A : Set} : Con A → Con A → Set where
    ■   : ε ⊆ ε
    ↑_  : ∀ {Γ : Con A} {Δ : Con A} {σ} (inc : Γ ⊆ Δ) → Γ ⊆ (Δ ∙ σ)
    _∙_ : ∀ {Γ : Con A} {Δ : Con A} (inc : Γ ⊆ Δ) σ → (Γ ∙ σ) ⊆ (Δ ∙ σ)

  {- properties of inclusion -}

  module Inclusion where

    refl : ∀ {A : Set} (Γ : Con A) → Γ ⊆ Γ
    refl ε       = ■
    refl (Γ ∙ σ) = refl Γ ∙ σ

    syntax refl Γ = same Γ

    _++_ : ∀ {A : Set} {Γ Δ Ε : Con A} → Γ ⊆ Δ → Δ ⊆ Ε → Γ ⊆ Ε
    ■       ++ pr₂      = pr₂
    pr₁ ∙ σ ++ ↑ pr₂    = ↑_ $ pr₁ ∙ σ ++ pr₂
    pr₁ ∙ σ ++ pr₂ ∙ .σ = (pr₁ ++ pr₂) ∙ σ
    ↑ pr₁   ++ ↑ pr₂    = ↑_ $ ↑ pr₁ ++ pr₂
    ↑ pr₁   ++ pr₂ ∙ σ  = ↑_ $ pr₁ ++ pr₂

 {-
    abstract

      ⊆-same-l : ∀ {A : Set} {Γ Δ : Con A} (pr : Γ ⊆ Δ) → ⊆-trans (same Γ) pr ≡ pr
      ⊆-same-l base = refl
      ⊆-same-l {A} {ε} (step inc) = refl
      ⊆-same-l {A} {_ ∙ _} (step inc) = cong step (⊆-same-l inc)
      ⊆-same-l (pop! inc) = cong pop! (⊆-same-l inc)

      ⊆-same-r : ∀ {A : Set} {Γ Δ : Con A} (pr : Γ ⊆ Δ) → ⊆-trans pr (same Δ) ≡ pr
      ⊆-same-r base = refl
      ⊆-same-r (step inc) = cong step (⊆-same-r inc)
      ⊆-same-r (pop! inc) = cong pop! (⊆-same-r inc)

      ⊆-same-swap : ∀ {A : Set} {Γ Δ : Con A} (pr : Γ ⊆ Δ) →
                    ⊆-trans pr (same Δ) ≡ ⊆-trans (same Γ) pr
      ⊆-same-swap pr = trans (⊆-same-r pr) (sym (⊆-same-l pr))

      ⊆-step-l : ∀ {A : Set} {Γ Δ Ε} {σ : A} (pr₁ : Γ ⊆ Δ) (pr₂ : Δ ⊆ Ε) →
                 step {A} {Γ} {Ε} {σ} (⊆-trans pr₁ pr₂) ≡ ⊆-trans (step pr₁) (pop! pr₂)
      ⊆-step-l base pr₂ = refl
      ⊆-step-l (step pr₁) pr₂ = refl
      ⊆-step-l (pop! pr₁) pr₂ = refl

      ⊆-step-r : ∀ {A : Set} {Γ Δ Ε} {σ : A} (pr₁ : Γ ⊆ Δ) (pr₂ : Δ ⊆ Ε) →
                 step {A} {Γ} {Ε} {σ} (⊆-trans pr₁ pr₂) ≡ ⊆-trans pr₁ (step pr₂)
      ⊆-step-r base pr₂ = refl
      ⊆-step-r (step pr₁) pr₂ = refl
      ⊆-step-r (pop! pr₁) pr₂ = refl

      ⊆-step-same : ∀ {A : Set} {Γ Δ} {σ : A} (pr : Γ ⊆ Δ) →
                    step {A} {Γ} {Δ} {σ} (⊆-trans (same Γ) pr) ≡ ⊆-trans pr (step (same Δ))
      ⊆-step-same pr = trans (cong step (sym (⊆-same-swap pr))) (⊆-step-r pr (same _))

      ⊆-step₂-same : ∀ {A : Set}  {Γ Δ} {σ τ : A} (pr : Γ ⊆ Δ) →
                     step {A} {Γ} {Δ ∙ σ} {τ} (step (⊆-trans (same Γ) pr))
                     ≡ ⊆-trans pr (step (step (same Δ)))
      ⊆-step₂-same pr = trans (cong step (⊆-step-same pr)) (⊆-step-r pr (step (same _)))

      ⊆-assoc : ∀ {A : Set} {Γ Δ Ε Φ : Con A} (pr₁ : Γ ⊆ Δ) (pr₂ : Δ ⊆ Ε) (pr₃ : Ε ⊆ Φ) →
        ⊆-trans pr₁ (⊆-trans pr₂ pr₃) ≡ ⊆-trans (⊆-trans pr₁ pr₂) pr₃
      ⊆-assoc base pr₂ pr₃ = refl
      ⊆-assoc (step pr₁) (step pr₂) (step pr₃) = cong step (⊆-assoc (step pr₁) (step pr₂) pr₃)
      ⊆-assoc (step pr₁) (step pr₂) (pop! pr₃) = cong step (⊆-assoc (step pr₁) pr₂ pr₃)
      ⊆-assoc (step pr₁) (pop! pr₂) (step pr₃) = cong step (⊆-assoc (step pr₁) (pop! pr₂) pr₃)
      ⊆-assoc (step pr₁) (pop! pr₂) (pop! pr₃) = cong step (⊆-assoc pr₁ pr₂ pr₃)
      ⊆-assoc (pop! pr₁) (step pr₂) (step pr₃) = cong step (⊆-assoc (pop! pr₁) (step pr₂) pr₃)
      ⊆-assoc (pop! pr₁) (step pr₂) (pop! pr₃) = cong step (⊆-assoc (pop! pr₁) pr₂ pr₃)
      ⊆-assoc (pop! pr₁) (pop! pr₂) (step pr₃) = cong step (⊆-assoc (pop! pr₁) (pop! pr₂) pr₃)
      ⊆-assoc (pop! pr₁) (pop! pr₂) (pop! pr₃) = cong pop! (⊆-assoc pr₁ pr₂ pr₃)
-}
{- definition of membership, truncate, etc. -}

module BelongsTo where

  open Context
  open Inclusion

  infix 4 _∈_
  data _∈_ {A : Set} (σ : A) : Con A → Set where
    zro : {Γ : Con A} → σ ∈ Γ ∙ σ
    suc : {Γ : Con A} {τ : A} (pr : σ ∈ Γ) → σ ∈ Γ ∙ τ

  have_actUpon_at_ : ∀ {A : Set} (f : A → Con A) → ∀ {σ : A} Γ (pr : σ ∈ Γ) → Con A
  have f actUpon Γ ∙ σ at zro    = Γ Context.++ f σ
  have f actUpon Γ ∙ τ at suc pr = have f actUpon Γ at pr ∙ τ

  abstract 

    suc-inj : ∀ {A : Set} {σ τ : A} {Γ} {pr₁ pr₂ : σ ∈ Γ}
              (eq : (σ ∈ Γ ∙ τ ∋ suc pr₁) ≡ suc pr₂) → pr₁ ≡ pr₂
    suc-inj Eq.refl = Eq.refl

  module BelongsTo where

    ∈ε-elim : ∀ {A : Set} {σ : A} (pr : σ ∈ ε) → ⊥
    ∈ε-elim ()

    map : ∀ {A B : Set} {σ : A} {Γ} (f : A → B) (pr : σ ∈ Γ) → f σ ∈ Context.map f Γ
    map f zro      = zro
    map f (suc pr) = suc $ map f pr

    _≟_ : ∀ {A} {σ : A} {Γ} (pr₁ pr₂ : σ ∈ Γ) → Dec (pr₁ ≡ pr₂)
    zro     ≟ zro     = yes Eq.refl
    zro     ≟ suc pr₂ = no (λ ())
    suc pr₁ ≟ zro     = no (λ ())
    suc pr₁ ≟ suc pr₂ with pr₁ ≟ pr₂
    ... | yes eq = yes $ Eq.cong suc eq
    ... | no ¬eq = no  $ ¬eq ∘ suc-inj

    wk : ∀ {A : Set} {σ : A} {Γ Δ : Con A} → Γ ⊆ Δ → σ ∈ Γ → σ ∈ Δ
    wk ■          ()
    wk (↑ incl)   pr       = suc $ wk incl pr
    wk (incl ∙ σ) zro      = zro
    wk (incl ∙ σ) (suc pr) = suc $ wk incl pr

    drop : ∀ {A} Γ {σ : A} (pr : σ ∈ Γ) → Con A
    drop (Γ ∙ σ) zro      = Γ
    drop (Γ ∙ τ) (suc pr) = drop Γ pr ∙ τ

    ∈++ˡ : ∀ {A Γ} Δ {σ : A} (pr : σ ∈ Γ) → σ ∈ Γ Context.++ Δ
    ∈++ˡ ε       pr = pr
    ∈++ˡ (Δ ∙ σ) pr = suc $ ∈++ˡ Δ pr

    ∈++ʳ : ∀ {A Γ Δ} {σ : A} (pr : σ ∈ Δ) → σ ∈ Γ Context.++ Δ
    ∈++ʳ zro      = zro
    ∈++ʳ (suc pr) = suc $ ∈++ʳ pr

    drop++ˡ : ∀ {A Γ} Δ {σ : A} (pr : σ ∈ Γ) →
              let open Context.Context in
              drop Γ pr ++ Δ ≡ drop (Γ ++ Δ) (∈++ˡ Δ pr)
    drop++ˡ ε       pr = Eq.refl
    drop++ˡ (Δ ∙ σ) pr = Eq.cong (flip _∙_ σ) $ drop++ˡ Δ pr
  
    drop++ʳ : ∀ {A Γ Δ} {σ : A} (pr : σ ∈ Δ) →
              let open Context.Context in
              Γ ++ drop Δ pr ≡ drop (Γ ++ Δ) (∈++ʳ pr)
    drop++ʳ zro              = Eq.refl
    drop++ʳ (suc {τ = τ} pr) = Eq.cong (flip _∙_ τ) $ drop++ʳ pr

    actAt++ˡ : ∀ {A Γ} Δ {σ : A} {f : A → Con A} (pr : σ ∈ Γ) →
               have f actUpon Γ Context.++ Δ at ∈++ˡ Δ pr
               ≡ (have f actUpon Γ at pr) Context.++ Δ
    actAt++ˡ ε       pr = Eq.refl
    actAt++ˡ (Δ ∙ σ) pr = Eq.cong (flip _∙_ σ) $ actAt++ˡ Δ pr

    subst : ∀ {A B Γ} {σ : A} (pr₁ : σ ∈ Γ) {f : A → Con B}
            {τ : B} (pr₂ : τ ∈ f σ)→ τ ∈ Context.subst Γ f
    subst {Γ = Γ ∙ σ} zro       {f} pr₂ = ∈++ˡ (Context.subst Γ f) pr₂
    subst             (suc pr₁)     pr₂ = ∈++ʳ (subst pr₁ pr₂)

{-

{- compatibility with inclusion -}

abstract

  inc-in-same : ∀ {A : Set} {Δ : Con A} {σ} (pr : σ ∈ Δ) → inc-in (same Δ) pr ≡ pr
  inc-in-same here! = refl
  inc-in-same (there pr) = cong there (inc-in-same pr)
  inc-in² : ∀ {A : Set} {Γ Δ Ε} {σ : A} (inc₁ : Γ ⊆ Δ) (inc₂ : Δ ⊆ Ε) (pr : σ ∈ Γ) →
            inc-in inc₂ (inc-in inc₁ pr) ≡ inc-in (⊆-trans inc₁ inc₂) pr
  inc-in² base inc₂ ()
  inc-in² (step inc₁) (step inc₂) pr = cong there (inc-in² (step inc₁) inc₂ pr)
  inc-in² (step inc₁) (pop! inc₂) pr = cong there (inc-in² inc₁ inc₂ pr)
  inc-in² (pop! inc₁) (step inc₂) pr = cong there (inc-in² (pop! inc₁) inc₂ pr)
  inc-in² (pop! inc₁) (pop! inc₂) here! = refl
  inc-in² (pop! inc₁) (pop! inc₂) (there pr) = cong there (inc-in² inc₁ inc₂ pr)

  inc-in-step : ∀ {A : Set} {Γ Δ σ} {γ : A} (inc : (Γ ∙ γ) ⊆ Δ) (pr : σ ∈ Γ) →
                inc-in (⊆-trans (step (same Γ)) inc) pr ≡ inc-in inc (there pr)
  inc-in-step {A} {ε} inc ()
  inc-in-step (step inc) pr = cong there (inc-in-step inc pr)
  inc-in-step {A} {Γ ∙ γ} (pop! inc) here! = cong there (sym (inc-in² (same (Γ ∙ γ)) inc here!))
  inc-in-step {A} {Γ ∙ γ} (pop! inc) (there pr) =
    cong there (trans (trans (sym (inc-in² (same (Γ ∙ γ)) inc (there pr)))
               (inc-in² (step (same Γ)) inc pr)) (inc-in-step inc pr))

{- properties of deletion -}

del : ∀ {A : Set} {Γ σ} (pr : σ ∈ Γ) → Con A
del {A} {ε} ()
del {A} {Γ ∙ _} here! = Γ
del {A} {Γ ∙ γ} (there pr) = (del pr) ∙ γ

pops : ∀ {A : Set} {Γ σ} (pr : σ ∈ Γ) → Con A
pops {A} {Γ ∙ _} here! = Γ
pops (there pr) = pops pr

abstract

  inc-del : ∀ {A : Set} {Γ Δ} {σ : A} (inc : Γ ⊆ Δ) (pr : σ ∈ Γ) → del pr ⊆ del (inc-in inc pr)
  inc-del base ()
  inc-del (step inc) pr = step (inc-del inc pr)
  inc-del (pop! inc) here! = inc
  inc-del (pop! inc) (there pr) = pop! (inc-del inc pr)

  inc-pops : ∀ {A : Set} {Γ Δ} {σ : A} (inc : Γ ⊆ Δ) (pr : σ ∈ Γ) → pops pr ⊆ pops (inc-in inc pr)
  inc-pops base ()
  inc-pops (step inc) pr = inc-pops inc pr
  inc-pops (pop! inc) here! = inc
  inc-pops (pop! inc) (there pr) = inc-pops inc pr
-}

module Interleaving where

  open Context
  open BelongsTo

  infix 5 _≡_⋈_
  infixl 5 _∙ˡ_ _∙ʳ_
  data _≡_⋈_ {A : Set} : (Γ Δ Ε : Con A) → Set where
    ε    : ε ≡ ε ⋈ ε
    _∙ʳ_ : ∀ {Γ Δ E} (pr : Γ ≡ Δ ⋈ E) σ → Γ ∙ σ ≡ Δ ⋈ E ∙ σ
    _∙ˡ_ : ∀ {Γ Δ E} (pr : Γ ≡ Δ ⋈ E) σ → Γ ∙ σ ≡ Δ ∙ σ ⋈ E

  module Interleaving where

    module RewriteRules where

      open Context.Context

      ⋈-assoc : {A : Set} (Γ₁ Γ₃ Δ₁ Δ₃ E₁ E₃ : Con A) {Γ₂ Δ₂ E₂ : Con A}
                (pr : (Γ₁ ++ Γ₂) ++ Γ₃ ≡ (Δ₁ ++ Δ₂) ++ Δ₃ ⋈ (E₁ ++ E₂) ++ E₃) →
                Γ₁ ++ (Γ₂ ++ Γ₃) ≡ Δ₁ ++ (Δ₂ ++ Δ₃) ⋈ E₁ ++ (E₂ ++ E₃)
      ⋈-assoc Γ₁ Γ₃ Δ₁ Δ₃ E₁ E₃ {Γ₂} {Δ₂} {E₂}
       rewrite assoc++ Γ₁ Γ₂ Γ₃ | assoc++ Δ₁ Δ₂ Δ₃ | assoc++ E₁ E₂ E₃ = id

      ⋈-assoc⁻¹ : {A : Set} (Γ₁ Γ₃ Δ₁ Δ₃ E₁ E₃ : Con A) {Γ₂ Δ₂ E₂ : Con A}
                  (pr : Γ₁ ++ (Γ₂ ++ Γ₃) ≡ Δ₁ ++ (Δ₂ ++ Δ₃) ⋈ E₁ ++ (E₂ ++ E₃)) →
                  (Γ₁ ++ Γ₂) ++ Γ₃ ≡ (Δ₁ ++ Δ₂) ++ Δ₃ ⋈ (E₁ ++ E₂) ++ E₃
      ⋈-assoc⁻¹ Γ₁ Γ₃ Δ₁ Δ₃ E₁ E₃ {Γ₂} {Δ₂} {E₂}
        rewrite assoc++ Γ₁ Γ₂ Γ₃ | assoc++ Δ₁ Δ₂ Δ₃ | assoc++ E₁ E₂ E₃ = id

    map : ∀ {A B} {Γ Δ E : Con A} (f : A → B) (pr : Γ ≡ Δ ⋈ E) →
          let open Context.Context in
          map f Γ ≡ map f Δ ⋈ map f E
    map f ε         = ε
    map f (pr ∙ʳ σ) = map f pr ∙ʳ f σ
    map f (pr ∙ˡ σ) = map f pr ∙ˡ f σ

    sym : ∀ {A} {Γ Δ E : Con A} (pr : Γ ≡ Δ ⋈ E) → Γ ≡ E ⋈ Δ
    sym ε         = ε
    sym (pr ∙ʳ σ) = sym pr ∙ˡ σ
    sym (pr ∙ˡ σ) = sym pr ∙ʳ σ

    reflˡ : ∀ {A} {Γ : Con A} → Γ ≡ Γ ⋈ ε
    reflˡ {A} {Γ} = helper Γ
      where
        helper : (Γ : Con A) → Γ ≡ Γ ⋈ ε
        helper ε       = ε
        helper (Γ ∙ σ) = helper Γ ∙ˡ σ

    reflʳ : ∀ {A} {Γ : Con A} → Γ ≡ ε ⋈ Γ
    reflʳ {A} {Γ} = sym reflˡ

    infixl 5 _++_ _ˡ++ʳ_
    _++_ : {A : Set} {Γ₁ Γ₂ Δ₁ Δ₂ E₁ E₂ : Con A}
           (pr₁ : Γ₁ ≡ Δ₁ ⋈ E₁) (pr₂ : Γ₂ ≡ Δ₂ ⋈ E₂) →
           let open Context.Context in Γ₁ ++ Γ₂ ≡ Δ₁ ++ Δ₂ ⋈ E₁ ++ E₂
    pr₁ ++ ε          = pr₁
    pr₁ ++ (pr₂ ∙ʳ σ) = pr₁ ++ pr₂ ∙ʳ σ
    pr₁ ++ (pr₂ ∙ˡ σ) = pr₁ ++ pr₂ ∙ˡ σ

    _ˡ++_ : {A : Set} (Γ : Con A) {Δ Δ₁ Δ₂ : Con A} (pr : Δ ≡ Δ₁ ⋈ Δ₂) →
          Γ Context.++ Δ ≡ Γ Context.++ Δ₁ ⋈ Δ₂
    Γ ˡ++ ε         = reflˡ
    Γ ˡ++ (pr ∙ʳ σ) = Γ ˡ++ pr ∙ʳ σ
    Γ ˡ++ (pr ∙ˡ σ) = Γ ˡ++ pr ∙ˡ σ

    _ʳ++_ : {A : Set} (Γ : Con A) {Δ Δ₁ Δ₂ : Con A} (pr : Δ ≡ Δ₁ ⋈ Δ₂) →
          Γ Context.++ Δ ≡ Δ₁ ⋈ Γ Context.++ Δ₂
    Γ ʳ++ pr = sym $ Γ ˡ++ sym pr

    _++ˡ_ : {A : Set} {Γ Γ₁ Γ₂ : Con A} (pr : Γ ≡ Γ₁ ⋈ Γ₂) (Δ : Con A) →
           Γ Context.++ Δ ≡ Γ₁ Context.++ Δ ⋈ Γ₂
    pr ++ˡ Δ = pr ++ reflˡ {Γ = Δ}

    _++ʳ_ : {A : Set} {Γ Γ₁ Γ₂ : Con A} (pr : Γ ≡ Γ₁ ⋈ Γ₂) (Δ : Con A) →
           Γ Context.++ Δ ≡ Γ₁ ⋈ Γ₂ Context.++ Δ
    pr ++ʳ Δ = pr ++ reflʳ {Γ = Δ}

    _ˡ++ʳ_ : {A : Set} (Γ Δ : Con A) → Γ Context.++ Δ ≡ Γ ⋈ Δ
    Γ ˡ++ʳ ε     = reflˡ
    Γ ˡ++ʳ Δ ∙ σ = Γ ˡ++ʳ Δ ∙ʳ σ

    _ʳ++ˡ_ : {A : Set} (Γ Δ : Con A) → Γ Context.++ Δ ≡ Δ ⋈ Γ
    Γ ʳ++ˡ Δ = sym $ Γ ˡ++ʳ Δ

    dropʳ : ∀ {A} Γ {σ : A} (pr : σ ∈ Γ) → Γ ≡ BelongsTo.drop Γ pr ⋈ ε ∙ σ
    dropʳ (Γ ∙ σ) zro      = reflˡ ∙ʳ σ
    dropʳ (Γ ∙ τ) (suc pr) = dropʳ Γ pr ∙ˡ τ

    dropˡ : ∀ {A} Γ {σ : A} (pr : σ ∈ Γ) → Γ ≡ ε ∙ σ ⋈ BelongsTo.drop Γ pr
    dropˡ Γ pr = sym $ dropʳ Γ pr

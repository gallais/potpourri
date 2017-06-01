module linear!.Language where

open import Agda.Builtin.Unit
open import Agda.Builtin.Nat hiding (_<_)

-- Types: base, lolli & bang
data   Type  : Set
record Type! : Set

infixr 4 _⊸_
data Type where
  `α    : Type
  _`⊸_ : Type! → Type! → Type

infix 6 _!^_
record Type! where
  inductive
  constructor _!^_
  field type  : Type
        bangs : Nat

pattern α = `α !^ 0
pattern _⊸_ σ τ = σ `⊸ τ !^ 0

infixl 5 _!
_! : Type! → Type!
σ !^ n ! = σ !^ suc n

infixl 3 _:>_ _□
-- Contexts: (boxed) snoc-lists of types
data Context : Nat → Set where
  ε    : Context 0
  _:>_ : {n : Nat} → Context n → Type! → Context (suc n)
  _□   : {n : Nat} → Context n → Context n

-- Usage: fresh or stale
infix 4 `fresh_ `stale_ fresh_ stale_
data Usage : Type → Set where
  `fresh_ : (σ : Type) → Usage σ
  `stale_ : (σ : Type) → Usage σ

`Usage! : Type! → Set
`Usage! (σ !^ 0) = Usage σ
`Usage! _        = ⊤

record Usage! (σ : Type!) : Set where
  constructor [_]
  field usage! : `Usage! σ
open Usage!

fresh_ : (σ : Type!) → Usage! σ
fresh σ !^ 0     = [ `fresh σ ]
fresh σ !^ suc m = [ tt       ]

stale_ : (σ : Type!) → Usage! σ
stale σ !^ 0     = [ `stale σ ]
stale σ !^ suc m = [ tt       ]

data Usages : {n : Nat} (γ : Context n) → Set where
  ε    : Usages ε
  _:>_ : {n : Nat} {γ : Context n} {σ : Type!} →
         Usages γ → Usage! σ → Usages (γ :> σ)
  _□   : {n : Nat} {γ : Context n} →
         Usages γ → Usages (γ □)


open import Data.Fin using (Fin ; zero ; suc)
-- De Bruijn index as resource consumption
infix 1 _⊢var_∈_⊠_
infixr 5 op_ wk_
data _⊢var_∈_⊠_ : {n : Nat} {γ : Context n}
                  (Γ : Usages γ) (k : Fin n) (σ : Type!) (Δ : Usages γ) → Set where
  z!  : {n : Nat} {γ : Context n} {Γ : Usages γ} {σ : Type} {m p : Nat} {S : Usage! (σ !^ suc m)} →
        Γ :> S ⊢var zero ∈ σ !^ p ⊠ Γ :> stale σ !^ suc m
  z0  : {n : Nat} {γ : Context n} {Γ : Usages γ} {σ : Type} →
        Γ :> (fresh σ !^ 0) ⊢var zero ∈ σ !^ 0 ⊠ Γ :> stale σ !^ 0
  wk_ : {n : Nat} {γ : Context n} {k : Fin n} {Γ Δ : Usages γ} {σ τ : Type!} {S : Usage! τ} →
        Γ ⊢var k ∈ σ ⊠ Δ → Γ :> S ⊢var suc k ∈ σ ⊠ Δ :> S
  op_ : {n : Nat} {γ : Context n} {k : Fin n} {Γ Δ : Usages γ} {σ : Type!} →
        Γ ⊢var k ∈ σ ! ⊠ Δ → Γ □ ⊢var k ∈ σ ⊠ Δ □

_ : ε :> fresh α ! ! ! ! ⊢var _ ∈ α ⊠ _
_ = z!

_ : ε :> fresh α ! ! ! ! □ □ ⊢var _ ∈ α ⊠ _
_ = op op z!

_ : ε :> fresh α ! ! ! ! □ :> stale α □ ⊢var _ ∈ α ⊠ _
_ = op wk op z!

open import Data.Empty
open import Data.Product

z-constraint : {n : Nat} (γ : Context (suc n)) (Γ : Usages γ) → Nat → Set
z-constraint (γ :> σ !^ zero)  (Γ :> [ `fresh .σ ]) zero = ⊤
z-constraint (γ :> σ !^ suc _) (Γ :> _)             _    = ⊤
z-constraint (γ □)             (Γ □)                m    = z-constraint γ Γ (suc m)
z-constraint (γ :> σ !^ zero)  (Γ :> _)             _    = ⊥

z-constraint-valid :
  {n : Nat} (γ : Context (suc n)) (Γ : Usages γ) (m : Nat) →
  z-constraint γ Γ m → Type × Usages γ
z-constraint-valid (γ :> σ !^ zero)  (Γ :> [ `fresh .σ ]) zero _  = σ , (Γ :> [ `stale σ ])
z-constraint-valid (γ :> σ !^ suc _) (Γ :> _)             _    _  = σ , (Γ :> [ tt ])
z-constraint-valid (γ □)             (Γ □)                m    pr =
  let (σ , Δ) = z-constraint-valid γ Γ (suc m) pr
  in (σ , (Δ □))
z-constraint-valid (γ :> σ !^ zero)  (Γ :> [ `fresh .σ ]) (suc _) ()
z-constraint-valid (γ :> σ !^ zero)  (Γ :> [ `stale .σ ]) _       ()


-- smart constructor for de Bruijn index 0
z : {n : Nat} {γ : Context (suc n)} {Γ : Usages γ}
    {m : Nat} {pr : z-constraint γ Γ m} →
    let (σ , Δ) = z-constraint-valid γ Γ m pr in
    Γ ⊢var zero ∈ σ !^ m ⊠ Δ
z {γ = γ :> σ !^ zero}  {Γ = Γ :> [ `fresh .σ ]} {m = zero}  = z0
z {γ = γ :> σ !^ suc _} {Γ = Γ :> _}             {m = _}     = z!
z {γ = γ □}             {Γ = Γ □}                {m = m}     = op z
z {γ = γ :> σ !^ zero}  {Γ = Γ :> [ `fresh .σ ]} {m = suc _} {pr = ()}
z {γ = γ :> σ !^ zero}  {Γ = Γ :> [ `stale .σ ]}             {pr = ()}

_ : ε :> fresh α ! ! ! ! ⊢var _ ∈ α ⊠ _
_ = z

_ : ε :> fresh α ! ! ! ! □ □ ⊢var _ ∈ α ⊠ _
_ = z

_ : ε :> fresh α ! ! ! ! □ :> stale α □ ⊢var _ ∈ α ⊠ _
_ = op wk z

data Infer (n : Nat) : Set
data Check (n : Nat) : Set

data Infer n where
  var : Fin n → Infer n
  cut : Check n → Type! → Infer n
  app : Infer n → Check n → Infer n

data Check n where
  lam : Check (suc n) → Check n
  neu : Infer n → Check n

infix 1 _⊢_∋_⊠_ _⊢_∈_⊠_

data _⊢_∈_⊠_ {n : Nat} {γ : Context n} (Γ : Usages γ) :
             (t : Infer n) (σ : Type!) (Δ : Usages γ) → Set

data _⊢_∋_⊠_ {n : Nat} {γ : Context n} (Γ : Usages γ) :
             (σ : Type!) (t : Check n) (Δ : Usages γ) → Set

data _⊢_∈_⊠_ {n} {γ} Γ where

  var : {k : Fin n} {σ : Type!} {Δ : Usages γ} →
        Γ ⊢var k  ∈ σ ⊠ Δ →
        Γ ⊢ var k ∈ σ ⊠ Δ

  cut : {t : Check n} {σ : Type} {Δ : Usages γ} →
        Γ ⊢ σ !^ 0 ∋ t ⊠ Δ →
        Γ ⊢ cut t (σ !^ 0) ∈ σ !^ 0 ⊠ Δ

  app : {f : Infer n} {t : Check n} {σ τ : Type!} {Δ Θ : Usages γ} →
        Γ ⊢ f ∈ σ ⊸ τ ⊠ Δ → Δ ⊢ σ ∋ t ⊠ Θ →
        Γ ⊢ app f t ∈ τ ⊠ Θ

  box : {t : Infer n} {σ : Type} {m : Nat} {Δ : Usages γ} →
        Γ □ ⊢ t ∈ σ !^ 0     ⊠ Δ □ →
        Γ   ⊢ t ∈ σ !^ suc m ⊠ Δ

data _⊢_∋_⊠_ {n} {γ} Γ where

  lam : {b : Check (suc n)} {σ τ : Type!} {Δ : Usages γ} →
        Γ :> fresh σ ⊢      τ ∋     b ⊠ Δ :> stale σ →
        Γ            ⊢ σ ⊸ τ ∋ lam b ⊠ Δ

  box : {t : Check n} {σ : Type} {m : Nat} {Δ : Usages γ} →
        Γ □ ⊢ σ !^ 0     ∋ t ⊠ Δ □ →
        Γ   ⊢ σ !^ suc m ∋ t ⊠ Δ


  neu : {t : Infer n} {σ : Type} {Δ : Usages γ} →
        Γ ⊢ t ∈ σ !^ 0     ⊠ Δ →
        Γ ⊢ σ !^ 0 ∋ neu t ⊠ Δ

-- examples
_ : ε ⊢ (α ⊸ α) ! ∋ _ ⊠ ε
_ = box (lam (neu (var z)))

_ : ε ⊢ α ! ⊸ α ! ∋ _ ⊠ ε
_ = lam (box (neu (var z)))

_ : ε ⊢ α ! ⊸ α ! ! ! ! ∋ _ ⊠ ε
_ = lam (box (neu (var z)))


open import Data.Nat.Base
open import Data.List as List hiding ([_] ; _∷ʳ_)
open import Data.List.All
open import Algebra
open import Function
open import Relation.Binary.PropositionalEquality

module LM {a} {A : Set a} = Monoid (List.monoid A)

Banged : Type! → Set
Banged = ((0 <_) ∘ Type!.bangs)

module _ {A : Set} where

 infix  1  _++_≅_
 infixr 20 _∷ˡ_ _∷ʳ_
 data _++_≅_ : (xs ys zs : List A) → Set where
   []   : [] ++ [] ≅ []
   _∷ˡ_ : (a : A) {xs ys zs : List A} → xs ++ ys ≅ zs → a ∷ xs ++ ys ≅ a ∷ zs
   _∷ʳ_ : (a : A) {xs ys zs : List A} → xs ++ ys ≅ zs → xs ++ a ∷ ys ≅ a ∷ zs

 infixr 20 _++ʳ_ _++ˡ_
 _++ʳ_ : {xs ys zs : List A} (ts : List A) (eq : xs ++ ys ≅ zs) →
         xs ++ ts List.++ ys ≅ ts List.++ zs
 []       ++ʳ eq = eq
 (t ∷ ts) ++ʳ eq = t ∷ʳ (ts ++ʳ eq)

 _++ˡ_ : {xs ys zs : List A} (ts : List A) (eq : xs ++ ys ≅ zs) →
         ts List.++ xs ++ ys ≅ ts List.++ zs
 []       ++ˡ eq = eq
 (t ∷ ts) ++ˡ eq = t ∷ˡ (ts ++ˡ eq)

 right : {xs : List A} → [] ++ xs ≅ xs
 right {xs = []}     = []
 right {xs = x ∷ xs} = x ∷ʳ right

 left : {xs : List A} → xs ++ [] ≅ xs
 left {xs = []}     = []
 left {xs = x ∷ xs} = x ∷ˡ left

 trivial : (xs ys : List A) → xs ++ ys ≅ xs List.++ ys
 trivial []       ys       = right
 trivial (x ∷ xs) ys       = x ∷ˡ trivial xs ys

 laivirt : (xs ys : List A) → ys ++ xs ≅ xs List.++ ys
 laivirt []       ys = left
 laivirt (x ∷ xs) ys = x ∷ʳ laivirt xs ys

-- This presentation of ILL is taken from:
-- http://llwiki.ens-lyon.fr/mediawiki/index.php/Intuitionistic_linear_logic
-- except for the `mix` constructor allowing the user to reorganise the
-- context (on the llwiki, the context is a multiset).

infix 1 _⊢_
data _⊢_ : List Type! → Type! → Set where
  ax  : {σ : Type!} →
        -------------
        (σ ∷ []) ⊢ σ
  cut : {γ δ : List Type!} {σ τ : Type!} →
        γ ⊢ σ → σ ∷ δ ⊢ τ →
        ---------------------
         γ ++ δ ⊢ τ
  ⊸R : {γ : List Type!} {σ τ : Type!} →
        σ ∷ γ ⊢ τ →
        -------------
        γ ⊢ σ ⊸ τ
  ⊸L : {γ δ : List Type!} {σ τ ν : Type!} →
        γ ⊢ σ → τ ∷ δ ⊢ ν →
        --------------------
        (σ ⊸ τ) ∷ γ ++ δ ⊢ ν

  !R : {γ : List Type!} {σ : Type!} →
       γ ⊢ σ → All Banged γ →
       ------------------------
       γ ⊢ σ !

  !dL : {γ : List Type!} {σ τ : Type!} →
        σ ∷ γ ⊢ τ →
        ------------
        (σ !) ∷ γ ⊢ τ

  !cL : {γ : List Type!} {σ τ : Type!} →
        (σ !) ∷ (σ !) ∷ γ ⊢ τ →
        --------------------
        (σ !) ∷ γ ⊢ τ

  !wL : {γ : List Type!} {σ τ : Type!} →
        γ ⊢ τ →
        --------
        (σ !) ∷ γ ⊢ τ

  mix : {γ δ θ : List Type!} {σ : Type!} →
        γ ++ δ ≅ θ → γ ++ δ ⊢ σ →
        --------------------------
        θ ⊢ σ

infix 1 _─_≡_─_
data _─_≡_─_ : {n : ℕ} {γ : Context n} (Γ Δ θ ξ : Usages γ) → Set where
  ε    : ε ─ ε ≡ ε ─ ε
  _:>⊘ : {n : ℕ} {γ : Context n} {Γ Δ θ ξ : Usages γ}
         {a : Type} {A B : Usage! (a !^ 0)} →
         Γ ─ Δ ≡ θ ─ ξ → Γ :> A ─ Δ :> A ≡ θ :> B ─ ξ :> B
  _:>[_!^suc_] :
          {n : ℕ} {γ : Context n} {Γ Δ θ ξ : Usages γ} →
          Γ ─ Δ ≡ θ ─ ξ →
          (a : Type) (m : ℕ) {A B : Usage! (a !^ suc m)} →
          Γ :> A ─ Δ :> A ≡ θ :> B ─ ξ :> B
  _:>_ : {n : ℕ} {γ : Context n} {Γ Δ θ ξ : Usages γ} → 
         Γ ─ Δ ≡ θ ─ ξ → (a : Type) →
         Γ :> [ `fresh a ] ─ Δ :> [ `stale a ] ≡
         θ :> [ `fresh a ] ─ ξ :> [ `stale a ]
  _□   : {n : ℕ} {γ : Context n} {Γ Δ θ ξ : Usages γ} →
         Γ ─ Δ ≡ θ ─ ξ →
         Γ □ ─ Δ □ ≡ θ □ ─ ξ □

infix 1 _⊆_
_⊆_ : {n : ℕ} {γ : Context n} (Γ Δ : Usages γ) → Set
Γ ⊆ Δ = Γ ─ Δ ≡ Γ ─ Δ

refl-⊆ : {n : ℕ} {γ : Context n} (Γ : Usages γ) → Γ ⊆ Γ
refl-⊆                       ε        = ε
refl-⊆ {γ = γ :> _ !^ 0}     (Γ :> S) = refl-⊆ Γ :>⊘
refl-⊆ {γ = γ :> a !^ suc m} (Γ :> S) = refl-⊆ Γ :>[ a !^suc m ]
refl-⊆                       (Γ □)    = refl-⊆ Γ □

trans-⊆ : {n : ℕ} {γ : Context n} {Γ Δ Θ : Usages γ} → Γ ⊆ Δ → Δ ⊆ Θ → Γ ⊆ Θ
trans-⊆ ε                   ε                   = ε
trans-⊆ (p :>⊘)             (q :>⊘)             = trans-⊆ p q :>⊘
trans-⊆ (p :>⊘)             (q :> a)            = trans-⊆ p q :> a
trans-⊆ (p :>[ a !^suc m ]) (q :>[ _ !^suc _ ]) = trans-⊆ p q :>[ a !^suc m ]
trans-⊆ (p :> a)            (q :>⊘)             = trans-⊆ p q :> a
trans-⊆ (p □)               (q □)               = trans-⊆ p q □

□-inv-⊆ : {n : ℕ} {γ : Context n} {Γ Δ : Usages γ} → Γ □ ⊆ Δ □ → Γ ⊆ Δ
□-inv-⊆ (pr □) = pr

:>-inv-⊆ : {n : ℕ} {γ : Context n} {Γ Δ : Usages γ}
           {σ : Type!} {S T : Usage! σ} →
           Γ :> S ⊆ Δ :> T → Γ ⊆ Δ
:>-inv-⊆ (pr :>⊘)             = pr
:>-inv-⊆ (pr :>[ _ !^suc _ ]) = pr
:>-inv-⊆ (pr :> a)            = pr

var-⊆ : {n : ℕ} {γ : Context n} {Γ Δ : Usages γ} {σ : Type!} {k : Fin n} →
        Γ ⊢var k ∈ σ ⊠ Δ → Γ ⊆ Δ
var-⊆                       z!     = refl-⊆ _ :>[ _ !^suc _ ]
var-⊆                       z0     = refl-⊆ _ :> _
var-⊆ {γ = γ :> a !^ 0}     (wk v) = var-⊆ v :>⊘
var-⊆ {γ = γ :> a !^ suc m} (wk v) = var-⊆ v :>[ a !^suc m ]
var-⊆                       (op v) = var-⊆ v □

infer-⊆ : {n : ℕ} {γ : Context n} {Γ Δ : Usages γ} {σ : Type!} {t : Infer n} →
          Γ ⊢ t ∈ σ ⊠ Δ → Γ ⊆ Δ
check-⊆ : {n : ℕ} {γ : Context n} {Γ Δ : Usages γ} {σ : Type!} {t : Check n} →
          Γ ⊢ σ ∋ t ⊠ Δ → Γ ⊆ Δ

infer-⊆ (var v)   = var-⊆ v
infer-⊆ (cut t)   = check-⊆ t
infer-⊆ (app f t) = trans-⊆ (infer-⊆ f) (check-⊆ t)
infer-⊆ (box t)   = □-inv-⊆ (infer-⊆ t)

check-⊆ (lam t) = :>-inv-⊆ (check-⊆ t)
check-⊆ (box t) = □-inv-⊆ (check-⊆ t)
check-⊆ (neu t) = infer-⊆ t

open import Agda.Builtin.Bool

banged : Type! → Bool
banged (_ !^ 0) = false
banged _        = true

all-banged : (γ : List Type!) → All Banged (filter banged γ)
all-banged []               = []
all-banged (σ !^ 0     ∷ γ) = all-banged γ
all-banged (σ !^ suc _ ∷ γ) = s≤s z≤n ∷ all-banged γ

soundz! : {σ : Type} (m p : Nat) → σ !^ suc m ∷ [] ⊢ σ !^ p
soundz! zero    zero    = !dL ax
soundz! zero    (suc p) = !R (soundz! zero p) (s≤s z≤n ∷ [])
soundz! (suc m) p       = !dL (soundz! m p)

⌞_⌟ : {n : ℕ} {γ : Context n} {Γ Δ : Usages γ} → Γ ⊆ Δ → List Type!
⌞ ε                 ⌟ = []
⌞ Γ :>⊘             ⌟ = ⌞ Γ ⌟
⌞ Γ :>[ a !^suc m ] ⌟ = a !^ suc m ∷ ⌞ Γ ⌟
⌞ Γ :> a            ⌟ = a !^ 0 ∷ ⌞ Γ ⌟
⌞ Γ □               ⌟ = ⌞ Γ ⌟

⌞_⌟≡⌞_⌟ : {n : ℕ} {γ : Context n} {Γ Δ : Usages γ} (p q : Γ ⊆ Δ) → ⌞ p ⌟ ≡ ⌞ q ⌟
⌞ ε                 ⌟≡⌞ ε                   ⌟ = refl
⌞ p :>⊘             ⌟≡⌞ q :>⊘               ⌟ = ⌞ p ⌟≡⌞ q ⌟
⌞ p :>[ a !^suc m ] ⌟≡⌞ q :>[ .a !^suc .m ] ⌟ = cong (_ ∷_) ⌞ p ⌟≡⌞ q ⌟
⌞ p :> a            ⌟≡⌞ q :> .a             ⌟ = cong (_ ∷_) ⌞ p ⌟≡⌞ q ⌟
⌞ p □               ⌟≡⌞ q □                 ⌟ = ⌞ p ⌟≡⌞ q ⌟

cons-snoc : ∀ {A : Set} xs (y : A) ys → xs ++ y ∷ ys ≡ (xs ++ y ∷ []) ++ ys
cons-snoc []       y ys = refl
cons-snoc (x ∷ xs) y ys = cong (x ∷_) (cons-snoc xs y ys)
 
⌞trans⌟ :
  {n : ℕ} {γ : Context n} {Γ Δ Θ : Usages γ} {σ : Type!}
  (δ : List Type!) (p : Γ ⊆ Δ) (q : Δ ⊆ Θ) →
  δ ++ (⌞ p ⌟ ++ ⌞ q ⌟) ⊢ σ → δ ++ ⌞ trans-⊆ p q ⌟ ⊢ σ
⌞trans⌟ δ ε                   ε                     t = t
⌞trans⌟ δ (p :>⊘)             (q :>⊘)               t = ⌞trans⌟ δ p q t
⌞trans⌟ δ (p :>⊘)             (q :> a)              t =
  mix (δ ++ʳ (a !^ 0) ∷ˡ right)
  $ ⌞trans⌟ (a !^ 0 ∷ δ) p q
  $ mix ((a !^ 0) ∷ʳ δ ++ˡ ⌞ p ⌟ ++ˡ right)
  $ subst (_⊢ _) (cong (_++ _) (cong (δ ++_) (sym $ proj₂ LM.identity _)))
  $ subst (_⊢ _) (sym $ LM.assoc δ ⌞ p ⌟ _) t
⌞trans⌟ δ (p :>[ a !^suc m ]) (q :>[ .a !^suc .m ]) t =
  mix (δ ++ʳ (a !^ suc m) ∷ˡ right) 
 $ !cL $ ⌞trans⌟ (a !^ suc m ∷ a !^ suc m ∷ δ) p q
 $ mix ((a !^ suc m) ∷ʳ (a !^ suc m) ∷ʳ δ ++ˡ ⌞ p ⌟ ++ˡ right)
 $ subst (_⊢ _) (cong (_++ _) (cong (δ ++_) (sym $ proj₂ LM.identity ⌞ p ⌟)))
 $ subst (_⊢ _) (sym $ LM.assoc δ ⌞ p ⌟ _)
 $ mix (δ ++ˡ ⌞ p ⌟ ++ʳ (a !^ suc m) ∷ˡ right)
 $ subst (_⊢ _) (cons-snoc δ (a !^ suc m) _)
 $ t
⌞trans⌟ δ (p :> a)            (q :>⊘)               t =
  subst (_⊢ _) (sym $ cons-snoc δ (a !^ 0) _)
  $ ⌞trans⌟ (δ ++ a !^ 0 ∷ []) p q
  $ subst (_⊢ _) (cons-snoc δ (a !^ 0) _) t
⌞trans⌟ δ (p □)               (q □)                 t = ⌞trans⌟ δ p q t

!wLs : {γ δ : List Type!} {σ : Type!} →
       All Banged δ → γ ⊢ σ → δ ++ γ ⊢ σ
!wLs []           t = t
!wLs (s≤s p ∷ ps) t = !wL (!wLs ps t)

!wLsᴿ : {γ δ : List Type!} {σ : Type!} →
        All Banged δ → γ ⊢ σ → γ ++ δ ⊢ σ
!wLsᴿ {γ} {δ} ps t = mix (laivirt γ δ) (!wLs ps t)


Banged-auto : {n : ℕ} {γ : Context n} {Γ : Usages γ} (p : Γ ⊆ Γ) →
              All Banged ⌞ p ⌟
Banged-auto ε                   = []
Banged-auto (p :>⊘)             = Banged-auto p
Banged-auto (p :>[ a !^suc m ]) = s≤s z≤n ∷ Banged-auto p
Banged-auto (p □)               = Banged-auto p

soundvar : {n : ℕ} {γ : Context n} {Γ Δ : Usages γ} {σ : Type!} {k : Fin n} →
           Γ ⊢var k ∈ σ ⊠ Δ → (p : Γ ⊆ Δ) → ⌞ p ⌟ ⊢ σ
soundvar z!     (p :>[ a !^suc m ]) = !wLsᴿ (Banged-auto p) (soundz! _ _)
soundvar z0     (p :> a)            = !wLsᴿ (Banged-auto p) ax
soundvar (wk T) (p :>⊘)             = soundvar T p
soundvar (wk T) (p :>[ a !^suc m ]) = !wL (soundvar T p)
soundvar (op T) (p □)               = rew $ cut (soundvar T p) (!dL ax)
  where rew = subst (_⊢ _) (proj₂ LM.identity _)


!Rs : {γ : List Type!} {σ : Type} (m : Nat) →
      γ ⊢ σ !^ 0 → All Banged γ →
      ------------------------
      γ ⊢ σ !^ suc m
!Rs zero    s c = !R s c
!Rs (suc m) s c = !R (!Rs m s c) c

sound∈ : {n : ℕ} {γ : Context n} {Γ Δ : Usages γ} {σ : Type!} {t : Infer n} →
         Γ ⊢ t ∈ σ ⊠ Δ →
         (p : Γ ⊆ Δ) → ⌞ p ⌟ ⊢ σ
sound∋ : {n : ℕ} {γ : Context n} {Γ Δ : Usages γ} {σ : Type!} {t : Check n} →
         Γ ⊢ σ ∋ t ⊠ Δ →
         (p : Γ ⊆ Δ) → ⌞ p ⌟ ⊢ σ

sound∈ (var V)   p = soundvar V p
sound∈ (cut T)   p = sound∋ T p
sound∈ (app F T) p =
  subst (_⊢ _) (⌞ trans-⊆ (infer-⊆ F) (check-⊆ T) ⌟≡⌞ p ⌟)
  $ ⌞trans⌟ [] (infer-⊆ F) (check-⊆ T)
  $ subst (_⊢ _) (cong (⌞ infer-⊆ F ⌟ ++_) (proj₂ LM.identity _))
  $ cut (sound∈ F (infer-⊆ F)) (⊸L (sound∋ T (check-⊆ T)) ax)
sound∈ (box T)   p = !Rs _ (sound∈ T (p □)) {!!}

sound∋ (box T)                  p = !Rs _ (sound∋ T (p □)) {!!}
sound∋ (neu T)                  p = sound∈ T p
sound∋ (lam {σ = σ !^ 0}     T) p = ⊸R (sound∋ T (p :> σ))
sound∋ (lam {σ = σ !^ suc m} T) p = ⊸R (sound∋ T (p :>[ σ !^suc m ]))

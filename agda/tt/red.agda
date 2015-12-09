module tt.red where

open import Data.Nat
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality as PEq using (_≡_)

open import tt.raw
open import tt.con
open import tt.env
open import tt.sem

infix 3 _[_⟩?_
data _[_⟩?_ {A : Set} (a : A) (R : A → A → Set) : (b : A) → Set where
  none  : a [ R ⟩? a
  some  : {b : A} → R a b → a [ R ⟩? b
  
infix 3 _[_⟩*_
data _[_⟩*_ {A : Set} (a : A) (R : A → A → Set) : (b : A) → Set where
  done  : a [ R ⟩* a
  more  : {b c : A} → R a b → b [ R ⟩* c → a [ R ⟩* c

to* : {A : Set} {R : A → A → Set} {a b : A} → a [ R ⟩? b → a [ R ⟩* b
to* none     = done
to* (some r) = more r done

mores : {A : Set} {a b c : A} {R : A → A → Set} → a [ R ⟩* b → b [ R ⟩* c → a [ R ⟩* c
mores done          red₂ = red₂
mores (more r red₁) red₂ = more r (mores red₁ red₂)

map[_,_,_,_,_,_⟩* : (A B : ℕ → Set) {m n : ℕ} (f : A m → B n)
            (R : IRel A) (S : IRel B) (F : {a a′ : A m} → R a a′ → S (f a) (f a′)) →
            {a a′ : A m} → a [ R ⟩* a′ → f a [ S ⟩* f a′
map[ A , B , f , R , S , F ⟩* done         = done
map[ A , B , f , R , S , F ⟩* (more r red) = more (F r) (map[ A , B , f , R , S , F ⟩* red)

wk[_,_⟩* : {A : ℕ → Set} {R : IRel A}
           (wk :  {m n : ℕ} (inc : m ⊆ n) → A m → A n)
           (wkR : {m n : ℕ} {a b : A m} (inc : m ⊆ n) → R a b → R (wk inc a) (wk inc b)) →
           {m n : ℕ} (inc : m ⊆ n) {a b : A m} → a [ R ⟩* b → wk inc a [ R ⟩* wk inc b
wk[_,_⟩* {A} {R} wk wkR inc = map[ A , A , wk inc , R , R , wkR inc ⟩*

record Syntax (E : ℕ → Set) : Set where
  eta-equality
  field
    weak  : Weakening E
    subst : Substituting Infer E

open Syntax public

SType : Syntax Type
weak  SType = weakT
subst SType = substT

SInfer : Syntax Infer
weak  SInfer = weakI
subst SInfer = substI

SCheck : Syntax Check
weak  SCheck = weakC
subst SCheck = substC

record Reduction {E : ℕ → Set} (SE : Syntax E) (_↝_ : IRel E) : Set where
  module SE = Syntax SE
  field
    weak↝       : {m n : ℕ} {a b : E m} (inc : m ⊆ n) → a ↝ b → SE.weak inc a ↝ SE.weak inc b
    subst↝      : {m n : ℕ} {a b : E m} (ρ : Var m =>[ Infer ] n) → a ↝ b → SE.subst a ρ ↝ SE.subst b ρ
    confluence  : {m : ℕ} {a b c : E m} → a [ _↝_ ⟩* b → a [ _↝_ ⟩* c →
                  ∃ λ d → b [ _↝_ ⟩* d × c [ _↝_ ⟩* d

  weak↝* : {m n : ℕ} {a b : E m} (inc : m ⊆ n) → a [ _↝_ ⟩* b → SE.weak inc a [ _↝_ ⟩* SE.weak inc b
  weak↝* inc = map[ E , E , SE.weak inc , _↝_ , _↝_ , weak↝ inc ⟩*

  subst↝* : {m n : ℕ} {a b : E m} (ρ : Var m =>[ Infer ] n) → a [ _↝_ ⟩* b → SE.subst a ρ [ _↝_ ⟩* SE.subst b ρ
  subst↝* ρ = map[ E , E , flip SE.subst ρ , _↝_ , _↝_ , subst↝ ρ ⟩*

record TypeReduction (_↝_ : IRel Type) : Set where
  field
    `set↝-inv : {m : ℕ} {ℓ : ℕ} {R : Type m} → `set ℓ ↝ R → R ≡ `set ℓ
    `nat↝-inv : {m : ℕ} {R : Type m} → `nat ↝ R → R ≡ `nat
    `pi↝-inv  : {m : ℕ} {A R : Type m} {B : Type (suc m)} →
                `pi A B ↝ R → ∃ λ ST → R ≡ uncurry `pi ST × A [ _↝_ ⟩? proj₁ ST × B [ _↝_ ⟩? proj₂ ST
    `sig↝-inv : {m : ℕ} {A R : Type m} {B : Type (suc m)} →
                `sig A B ↝ R → ∃ λ ST → R ≡ uncurry `sig ST × A [ _↝_ ⟩? proj₁ ST × B [ _↝_ ⟩? proj₂ ST
    β↝        : {m : ℕ} (T : Type (suc m)) {u : Check m} {U U′ : Type m} →
                U ↝ U′ → Substitution ⊨ T ⟨ `ann u U /0⟩T [ _↝_ ⟩* Substitution ⊨ T ⟨ `ann u U′ /0⟩T
                    
  `set↝*-inv : {m : ℕ} {ℓ : ℕ} {R : Type m} → `set ℓ [ _↝_ ⟩* R → R ≡ `set ℓ
  `set↝*-inv done         = PEq.refl
  `set↝*-inv (more r red) with `set↝-inv r
  ... | PEq.refl = `set↝*-inv red
  
  `nat↝*-inv : {m : ℕ} {R : Type m} → `nat [ _↝_ ⟩* R → R ≡ `nat
  `nat↝*-inv done         = PEq.refl
  `nat↝*-inv (more r red) with `nat↝-inv r
  ... | PEq.refl = `nat↝*-inv red

  `pi↝*-inv : {m : ℕ} {A R : Type m} {B : Type (suc m)} →
              `pi A B [ _↝_ ⟩* R → ∃ λ ST → R ≡ uncurry `pi ST × A [ _↝_ ⟩* proj₁ ST × B [ _↝_ ⟩* proj₂ ST
  `pi↝*-inv done         = , PEq.refl , done , done
  `pi↝*-inv (more r red) with `pi↝-inv r
  ... | ((S , T) , PEq.refl , r₁ , r₂) = map id (map id (map (mores (to* r₁)) (mores (to* r₂)))) $ `pi↝*-inv red

  `sig↝*-inv : {m : ℕ} {A R : Type m} {B : Type (suc m)} →
              `sig A B [ _↝_ ⟩* R → ∃ λ ST → R ≡ uncurry `sig ST × A [ _↝_ ⟩* proj₁ ST × B [ _↝_ ⟩* proj₂ ST
  `sig↝*-inv done         = , PEq.refl , done , done
  `sig↝*-inv (more r red) with `sig↝-inv r
  ... | ((S , T) , PEq.refl , r₁ , r₂) = map id (map id (map (mores (to* r₁)) (mores (to* r₂)))) $ `sig↝*-inv red

  β↝* : {m : ℕ} (T : Type (suc m)) {u : Check m} {U U′ : Type m} →
        U [ _↝_ ⟩* U′ → Substitution ⊨ T ⟨ `ann u U /0⟩T [ _↝_ ⟩* Substitution ⊨ T ⟨ `ann u U′ /0⟩T
  β↝* T done         = done
  β↝* T (more r red) = mores (β↝ T r) (β↝* T red)

record WeakHead (f : Type ⇒ Type) (_↝_ : IRel Type) : Set where
  field
    yieldsWhnf   : {n : ℕ} (t : Type n) → Type f t ≡^Con f t
    yieldsReduct : {n : ℕ} (t : Type n) → t [ _↝_ ⟩* f t
    uncoversHead : {n : ℕ} (t : Type n) (ex : ∃ λ s → (t [ _↝_ ⟩* s) × Type s ≡^Con s) →
                   Type f t ≡^Con proj₁ ex

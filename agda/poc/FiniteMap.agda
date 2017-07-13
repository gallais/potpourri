module poc.FiniteMap where

open import Function
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

record _↔_ (A B : Set) : Set where
  field push : A → B
        pull : B → A
open _↔_

↔-refl : {A : Set} → A ↔ A
push ↔-refl = id
pull ↔-refl = id

open import Data.Unit using (⊤ ; tt)
open import Data.Empty
import Data.Empty.Irrelevant as Irr

IsYes : {A : Set} → Dec A → Set
IsYes (no _)  = ⊥
IsYes (yes _) = ⊤

.trivial : {A : Set} {{a : A}} → A
trivial {{a}} = a


module TrichotomousSpec
       {A : Set}
       (_⋖_     : A → A → Set)
       (_⋖?_    : Trichotomous _≡_ _⋖_)
       where

  open import Data.Product

  ∃₃ : {A B C : Set} → (A → B → C → Set) → Set
  ∃₃ f = ∃ λ a → ∃ λ b → ∃ λ c → f a b c

  ≈ : {x y : A} → .(x ≡ y) → ∃₃ (λ a b c → x ⋖? y ≡ tri≈ a b c)
  ≈ {x} {y} eq with x ⋖? y
  ... | tri< a ¬b ¬c = Irr.⊥-elim (¬b eq)
  ... | tri≈ ¬a b ¬c = , , , refl
  ... | tri> ¬a ¬b c = Irr.⊥-elim (¬b eq)

  < : {x y : A} → .(x ⋖ y) → ∃₃ (λ a b c → x ⋖? y ≡ tri< a b c)
  < {x} {y} lt with x ⋖? y
  ... | tri< a ¬b ¬c = , , , refl
  ... | tri≈ ¬a b ¬c = Irr.⊥-elim (¬a lt)
  ... | tri> ¬a ¬b c = Irr.⊥-elim (¬a lt)

  > : {x y : A} → .(y ⋖ x) → ∃₃ (λ a b c → x ⋖? y ≡ tri> a b c)
  > {x} {y} gt with x ⋖? y
  ... | tri< a ¬b ¬c = Irr.⊥-elim (¬c gt)
  ... | tri≈ ¬a b ¬c = Irr.⊥-elim (¬c gt)
  ... | tri> ¬a ¬b c = , , , refl

module Lift {A : Set}
            (_⋖_     : A → A → Set)
            (_⋖?_    : Trichotomous _≡_ _⋖_)
            (⋖-trans : Transitive _⋖_)
             where

  data Bnd : Set where
    -∞ +∞ : Bnd
    lift  : A → Bnd

  lift-inj : {a b : A} → lift a ≡ lift b → a ≡ b
  lift-inj refl = refl

  data _<_ : Bnd → Bnd → Set where
    instance
      -∞<_  : (a : A) → -∞ < lift a
      _<+∞  : (a : A) → lift a < +∞
      -∞<+∞ : -∞ < +∞
    lift  : {a b : A} → a ⋖ b → lift a < lift b

  open import Data.Sum
  _≤_ : Bnd → Bnd → Set
  a ≤ b = a < b ⊎ a ≡ b

  <-trans : {a b c : Bnd} → a < b → b < c → a < c
  <-trans (-∞< .a) (a <+∞)  = -∞<+∞
  <-trans (lift p) (a <+∞)  = _ <+∞
  <-trans (-∞< a)  (lift q) = -∞< _
  <-trans (lift p) (lift q) = lift (⋖-trans p q)
  <-trans () (-∞< a)
  <-trans () -∞<+∞

  ≤-trans : {a b c : Bnd} → a ≤ b → b ≤ c → a ≤ c
  ≤-trans (inj₁ p)    (inj₁ q)    = inj₁ (<-trans p q)
  ≤-trans (inj₂ refl) q           = q
  ≤-trans p           (inj₂ refl) = p

  ≤<-trans : {a b c : Bnd} → a ≤ b → b < c → a < c
  ≤<-trans (inj₁ p)    q = <-trans p q
  ≤<-trans (inj₂ refl) q = q

  <≤-trans : {a b c : Bnd} → a < b → b ≤ c → a < c
  <≤-trans p (inj₁ q)    = <-trans p q
  <≤-trans p (inj₂ refl) = p

  <-lift-inj : {a b : A} → lift a < lift b → a ⋖ b
  <-lift-inj (lift a<b) = a<b

  _<?_ : Trichotomous _≡_ _<_
  -∞     <? -∞     = tri≈ (λ ()) refl (λ ())
  -∞     <? +∞     = tri< -∞<+∞ (λ ()) (λ ())
  -∞     <? lift _ = tri< (-∞< _) (λ ()) (λ ())
  +∞     <? -∞     = tri> (λ ()) (λ ()) -∞<+∞
  +∞     <? +∞     = tri≈ (λ ()) refl (λ ())
  +∞     <? lift _ = tri> (λ ()) (λ ()) (_ <+∞)
  lift _ <? -∞     = tri> (λ ()) (λ ()) (-∞< _)
  lift _ <? +∞     = tri< (_ <+∞) (λ ()) (λ ())
  lift x <? lift y with x ⋖? y
  ... | tri< a ¬b ¬c = tri< (lift a) (¬b ∘ lift-inj) (¬c ∘ <-lift-inj)
  ... | tri≈ ¬a b ¬c = tri≈ (¬a ∘ <-lift-inj) (cong lift b) (¬c ∘ <-lift-inj)
  ... | tri> ¬a ¬b c = tri> (¬a ∘ <-lift-inj) (¬b ∘ lift-inj) (lift c)

  <-irrefl : {x : Bnd} → .(x < x) → ⊥
  <-irrefl {x} x<x with x <? x
  ... | tri< a ¬b ¬c = ¬b refl
  ... | tri≈ ¬a b ¬c = Irr.⊥-elim (¬a x<x)
  ... | tri> ¬a ¬b c = ¬b refl

  instance
    ilift : {a b : A} → {{pr : a ⋖ b}} → lift a < lift b
    ilift {{pr}} = lift pr

  infixr 5 _∷_
  data SL : Bnd → Bnd → Set where
    []  : {a b : Bnd} .{{a<b : a < b}} → SL a b
    _∷_ : {a b : Bnd} (x : A) → SL (lift x) b → .{{a<x : a < lift x}} → SL a b

  infix 3 _∈_
  data _∈_ (x : A) {a b : Bnd} : SL a b → Set where
    z : .{{a<b : a < lift x}} {xs : SL (lift x) b} → x ∈ x ∷ xs
    s : {y : A} .{{a<b : a < lift y}} {xs : SL (lift y) b} → x ∈ xs → x ∈ y ∷ xs

  x≤xs→x∉xs : {x : A} {a b : Bnd} .{{x<a : lift x ≤ a}} {xs : SL a b} →
              ¬ (x ∈ xs)
  x≤xs→x∉xs {x} {a} z     = ⊥-elim (<-irrefl p) where
    .p : a < a
    p = <≤-trans ((a < lift x) ∋ trivial) trivial
  x≤xs→x∉xs {x} {a} (s n) = x≤xs→x∉xs {{p}} n where
    .p : lift x ≤ lift _
    p = ≤-trans (lift x ≤ a ∋ trivial) (inj₁ trivial)

  ∈-unique : {x : A} {a b : Bnd} {xs : SL a b} (p q : x ∈ xs) → p ≡ q
  ∈-unique z     z     = refl
  ∈-unique z     (s q) = ⊥-elim (x≤xs→x∉xs {{inj₂ refl}} q)
  ∈-unique (s p) z     = ⊥-elim (x≤xs→x∉xs {{inj₂ refl}} p)
  ∈-unique (s p) (s q) = cong s (∈-unique p q)

  x∈y∷xs-inv : {x y : A} {a b : Bnd} .{{a<y : a < lift y}} {xs : SL (lift y) b} →
               x ∈ (SL a b ∋ y ∷ xs) → x ≡ y ⊎ x ∈ xs
  x∈y∷xs-inv z     = inj₁ refl
  x∈y∷xs-inv (s n) = inj₂ n

  sllookup : (x : A) {a b : Bnd} (xs : SL a b) → Dec (x ∈ xs)
  sllookup x []       = no (λ ())
  sllookup x (y ∷ xs) with x ⋖? y
  ... | tri< a ¬b ¬c = no ([ ¬b , x≤xs→x∉xs {{inj₁ (lift a)}} ]′ ∘ x∈y∷xs-inv)
  ... | tri≈ ¬a b ¬c = yes (subst (_∈ _) (sym b) z)
  ... | tri> ¬a ¬b c with sllookup x xs
  ... | yes p = yes (s p)
  ... | no ¬p = no ([ ¬b , ¬p ]′ ∘ x∈y∷xs-inv)

  slinsert : (v : A) {a b : Bnd} {{a<v : a < lift v}} {{v<b : lift v < b}} → SL a b → SL a b
  slinsert v []       = v ∷ []
  slinsert v (x ∷ xs) with v ⋖? x
  ... | tri< a _ _ = let instance p = a in v ∷ x ∷ xs
  ... | tri≈ _ _ _ = x ∷ xs
  ... | tri> _ _ c = let instance p = c in x ∷ slinsert v xs

  sldowncast : {a b : Bnd} (v : Bnd) .{{v<a : v < a}} → SL a b → SL v b
  sldowncast {a} v []       = [] {{<-trans (v < a ∋ trivial) trivial}}
  sldowncast {a} v (x ∷ xs) = (x ∷ xs) {{<-trans (v < a ∋ trivial) trivial}}

  sldelete : (v : A) {a b : Bnd} {{a<v : a < lift v}} {{v<b : lift v < b}} → SL a b → SL a b
  sldelete v []       = []
  sldelete v (x ∷ xs) with v ⋖? x
  ... | tri< _ _ _ = x ∷ xs
  ... | tri≈ _ _ _ = sldowncast _ xs
  ... | tri> _ _ c = let instance p = c in x ∷ sldelete v xs

  SL-ext : {a b : Bnd} (xs ys : SL a b) → Set
  SL-ext xs ys = ∀ x → IsYes (sllookup x xs) ↔ IsYes (sllookup x ys)

  open import Data.Product
  module ⋖?-spec = TrichotomousSpec _⋖_ _⋖?_

  sllookup-≤ : {a b : Bnd} (x : A) .{{x≤a : lift x ≤ a}} (xs : SL a b) →
               ∃ λ pr → sllookup x xs ≡ no pr
  sllookup-≤ x []       = , refl
  sllookup-≤ {a} x (y ∷ xs)
    with ⋖?-spec.< (x ⋖ y ∋ <-lift-inj (≤<-trans trivial ((a < lift y) ∋ trivial)))
  ... | (_ , _ , _ , eq) rewrite eq = , refl

  SL-ext-tail : {a b : Bnd} {x : A} .{{a<x : a < lift x}} {xs ys : SL (lift x) b} →
                SL-ext (SL a b ∋ x ∷ xs) (x ∷ ys) → SL-ext xs ys
  SL-ext-tail {x = x} {xs = xs} {ys} ext y with y ⋖? x | ext y
  SL-ext-tail {x = x} {xs = xs} {ys} ext y | tri< a ¬b ¬c | p
    rewrite proj₂ (sllookup-≤ y {{inj₁ (lift a)}} xs)
          | proj₂ (sllookup-≤ y {{inj₁ (lift a)}} ys) = ↔-refl
  SL-ext-tail {x = x} {xs = xs} {ys} ext y | tri≈ ¬a b ¬c | p
    rewrite proj₂ (sllookup-≤ y {{inj₂ (cong lift b)}} xs)
          | proj₂ (sllookup-≤ y {{inj₂ (cong lift b)}} ys) = ↔-refl
  SL-ext-tail {x = x} {xs = xs} {ys} ext y | tri> ¬a ¬b c | p
    with sllookup y xs | sllookup y ys
  ... | yes _ | yes _ = ↔-refl
  ... | yes _ | no _  = p
  ... | no _  | yes _ = p
  ... | no _  | no _  = ↔-refl

  slintensional : {a b : Bnd} (xs ys : SL a b) → SL-ext xs ys → xs ≡ ys
  slintensional []       []       ext = refl
  slintensional []       (x ∷ ys) ext
    with ⋖?-spec.≈ (x ≡ x ∋ refl) | pull (ext x)
  ... | (¬a , b , ¬c , eq) | p rewrite eq = ⊥-elim (p tt)
  slintensional (x ∷ xs) []       ext
    with ⋖?-spec.≈ (x ≡ x ∋ refl) | push (ext x)
  ... | (¬a , b , ¬c , eq) | p rewrite eq = ⊥-elim (p tt)
  slintensional (x ∷ xs) (y ∷ ys) ext with x ⋖? y
  ... | tri< a ¬b ¬c
    with ⋖?-spec.< a | ⋖?-spec.≈ (x ≡ x ∋ refl) | push (ext x)
  ... | (_ , _ , _ , eq) | (_ , _ , _ , eq') | p
    rewrite eq | eq' = ⊥-elim (p tt)
  slintensional (x ∷ xs) (y ∷ ys) ext
    | tri≈ ¬a refl ¬c = cong (x ∷_) (slintensional xs ys (SL-ext-tail ext))
  slintensional (x ∷ xs) (y ∷ ys) ext
    | tri> ¬a ¬b c
    with ⋖?-spec.< c | ⋖?-spec.≈ (y ≡ y ∋ refl) | pull (ext y)
  ... | (_ , _ , _ , eq) | (_ , _ , _ , eq') | p
    rewrite eq | eq' = ⊥-elim (p tt)

module IntMap where

  open import Data.Nat as ℕ using (ℕ ; compare)
  open import Data.Nat.Properties
  open import Function
  open Lift ℕ._<_ <-cmp <-trans
  open import Data.Unit
  open import Data.Product

  Values : {a b : Bnd} → SL a b → Set → Set
  Values []        A = ⊤
  Values (x ∷ xs)  A = A × Values xs A

  record IntMap (A : Set) : Set where
    constructor mkIntMap
    field indices : SL -∞ +∞
          values  : Values indices A
  open IntMap public

  mempty : {A : Set} → IntMap A
  mempty = mkIntMap [] tt

  msingleton : {A : Set} → ℕ → A → IntMap A
  msingleton n a = mkIntMap (n ∷ []) (a , tt)

  vlookup : {A : Set} {n : ℕ} {a b : Bnd} {xs : SL a b} → n ∈ xs → Values xs A → A
  vlookup z     (v , _)  = v
  vlookup (s n) (_ , vs) = vlookup n vs

  open import Data.Maybe

  mlookup : {A : Set} (n : ℕ) → IntMap A → Maybe A
  mlookup n m with sllookup n (indices m)
  ... | yes p = just (vlookup p (values m))
  ... | no ¬p = nothing

  vinsert : {A : Set} (n : ℕ) → {a b : Bnd} {{a<n : a < lift n}} {{n<b : lift n < b}} →
            A → (xs : SL a b) → Values xs A → Values (slinsert n xs) A
  vinsert n a []       vs = a , tt
  vinsert n a (x ∷ xs) vs with <-cmp n x
  ... | tri< _ _ _ = a , vs
  ... | tri≈ _ _ _ = a , proj₂ vs
  ... | tri> _ _ c = let instance p = c in proj₁ vs , vinsert n a xs (proj₂ vs)

  minsert : {A : Set} (n : ℕ) → A → IntMap A → IntMap A
  minsert n a m = mkIntMap _ $ vinsert n a (indices m) (values m)

  vdelete : {A : Set} (n : ℕ) → {a b : Bnd} {{a<n : a < lift n}} {{n<b : lift n < b}} →
            (xs : SL a b) → Values xs A → Values (sldelete n xs) A
  vdelete n []       vs = vs
  vdelete n (x ∷ xs) vs with <-cmp n x
  ... | tri< _ _ _ = vs
  ... | tri> _ _ c = let instance p = c in proj₁ vs , vdelete n xs (proj₂ vs)
  vdelete n (x ∷ [])    vs | tri≈ _ _ _ = tt
  vdelete n (x ∷ _ ∷ _) vs | tri≈ _ _ _ = proj₂ vs

  mdelete : {A : Set} (n : ℕ) → IntMap A → IntMap A
  mdelete n m = mkIntMap _ $ vdelete n (indices m) (values m)

  Values-ext : {A : Set} {a b : Bnd} {xs : SL a b} (vs ws : Values xs A) → Set
  Values-ext vs ws = ∀ {n} (n : n ∈ _) → vlookup n vs ≡ vlookup n ws


  vintensional : {A : Set} {a b : Bnd} (xs : SL a b) (vs ws : Values xs A) → Values-ext vs ws → vs ≡ ws
  vintensional []       vs ws ext = refl
  vintensional (x ∷ xs) vs ws ext = let ih = vintensional xs (proj₂ vs) (proj₂ ws) (ext ∘ s)
                                    in cong₂ _,_ (ext z) ih

  IntMap-ext : {A : Set} (m₁ m₂ : IntMap A) → Set
  IntMap-ext m₁ m₂ = ∀ n → mlookup n m₁ ≡ mlookup n m₂

  IntMap→SL-ext : {A : Set} (m₁ m₂ : IntMap A) → IntMap-ext m₁ m₂ → SL-ext (indices m₁) (indices m₂)
  IntMap→SL-ext m₁ m₂ ext n with sllookup n (indices m₁) | sllookup n (indices m₂) | ext n
  ... | yes _  | yes _ | _  = ↔-refl
  ... | no _   | no _  | _  = ↔-refl
  ... | yes _  | no _  | ()
  ... | no _   | yes _ | ()

  just-inj : {A : Set} {a b : A} → (Maybe A ∋ just a) ≡ just b → a ≡ b
  just-inj refl = refl

  IntMap→Values-ext : {A : Set} {xs : SL -∞ +∞} (vs ws : Values xs A) →
                      IntMap-ext (mkIntMap _ vs) (mkIntMap _ ws) → Values-ext vs ws
  IntMap→Values-ext {A} {xs} vs ws ext {n} n∈xs with sllookup n xs | ext n
  ... | yes n∈xs′ | q = subst _ (∈-unique n∈xs′ n∈xs) (just-inj q)
  ... | no ¬n∈xs  | q = ⊥-elim (¬n∈xs n∈xs)

  open ≡-Reasoning

  mintensional : {A : Set} (m₁ m₂ : IntMap A) → IntMap-ext m₁ m₂ → m₁ ≡ m₂
  mintensional m₁@(mkIntMap i₁ v₁) m₂@(mkIntMap i₂ v₂) ext = begin
    mkIntMap i₁ v₁                 ≡⟨ cast eqi₁₂               ⟩
    mkIntMap i₂ (subst _ eqi₁₂ v₁) ≡⟨ cong (mkIntMap i₂) eqv₁₂ ⟩
    mkIntMap i₂ v₂ ∎

   where

     eqi₁₂ : i₁ ≡ i₂
     eqi₁₂ = slintensional _ _ (IntMap→SL-ext m₁ m₂ ext)

     cast : {A : Set} {i₁ i₂ : SL -∞ +∞} (eq : i₁ ≡ i₂) {v₁ : Values i₁ A} →
            mkIntMap i₁ v₁ ≡ mkIntMap i₂ (subst _ eq v₁)
     cast refl = refl

     ext' : IntMap-ext (mkIntMap i₂ (subst _ eqi₁₂ v₁)) m₂
     ext' n = begin
       mlookup n (mkIntMap i₂ (subst _ eqi₁₂ v₁)) ≡⟨ cong (mlookup n) (sym (cast eqi₁₂)) ⟩
       mlookup n m₁                               ≡⟨ ext n ⟩
       mlookup n m₂ ∎

     eqv₁₂ : subst _ eqi₁₂ v₁ ≡ v₂
     eqv₁₂ = vintensional i₂ (subst _ eqi₁₂ v₁) v₂ (IntMap→Values-ext _ _ ext')


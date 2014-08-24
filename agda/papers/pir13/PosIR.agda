-- The content of this file is derived from Ghani, Malatesta &
-- Nordvall-Forsberg's "Positive Inductive-Recursive Definitions"
-- It is mostly a cleaned-up version of NF's formalization.

open import Level
open import Categories.Category

module PosIR {o m e : Level} (ℂ : Category o m e) where

module C = Category ℂ
open C using (Obj ; _⇒_)
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Function

mutual

  data IR+ (ℓ : Level) : Set (suc ℓ ⊔ m ⊔ o) where
    ι : (c : Obj) → IR+ ℓ
    σ : (A : Set ℓ) (f : A → IR+ ℓ) → IR+ ℓ
    δ : (A : Set ℓ) (F : (A → Obj) → IR+ ℓ) (F→ : [ F ]→) → IR+ ℓ

  [_]→ : {ℓ : Level} {A : Set ℓ} (F : (A → Obj) → IR+ ℓ) → Set (suc ℓ ⊔ m ⊔ o)
  [_]→ {ℓ} {A} F = ∀ {f g : A → Obj} (η : (a : A) → f a ⇒ g a) → IR+[ F f , F g ]

  data IR+[_,_] {ℓ : Level} : (γ₁ γ₂ : IR+ ℓ) → Set (suc ℓ ⊔ m ⊔ o) where
    Γγγ : {γ : IR+ ℓ} → IR+[ γ , γ ]
    Γιι : {c₁ c₂ : Obj} (g : c₁ ⇒ c₂) → IR+[ ι c₁ , ι c₂ ]
    Γισ : {c : Obj} {A : Set ℓ} {f : A → IR+ ℓ}
          (a : A) (Γιf : IR+[ ι c , f a ]) → IR+[ ι c , σ A f ]
    Γιδ : {c : Obj} {A : Set ℓ} {F : (A → Obj) → IR+ ℓ} {F→ : [ F ]→}
          (g : A → ⊥) (ΓιF : IR+[ ι c , F (⊥-elim ∘ g) ]) → IR+[ ι c , δ A F F→ ]
    Γσγ : {A : Set ℓ} {f : A → IR+ ℓ} {γ : IR+ ℓ}
          (Γfγ : (a : A) → IR+[ f a , γ ]) → IR+[ σ A f , γ ]
    Γδγ : {A : Set ℓ} {F : (A → Obj) → IR+ ℓ} {F→ : [ F ]→} {γ : IR+ ℓ}
          (ΓFγ : (g : A → Obj) → IR+[ F g , γ ]) → IR+[ δ A F F→ , γ ]
    Γδσ : {A : Set ℓ} {F : (A → Obj) → IR+ ℓ} {F→ : [ F ]→}
          {B : Set ℓ} {f : B → IR+ ℓ} →
          (b : B) (ΓFf : (g : A → Obj) → IR+[ F g , f b ]) → IR+[ δ A F F→ , σ B f ]
    Γδδ : {A : Set ℓ} {F : (A → Obj) → IR+ ℓ} {F→ : [ F ]→}
          {B : Set ℓ} {G : (B → Obj) → IR+ ℓ} {G→ : [ G ]→} →
          (g : B → A) (ΓFG : (h : A → Obj) → IR+[ F h , G $ h ∘ g ]) →
          IR+[ δ A F F→ , δ B G G→ ]

_∘IR+_ : {ℓ : Level} {γ₁ γ₂ γ₃ : IR+ ℓ}
         (Γ₂₃ : IR+[ γ₂ , γ₃ ]) (Γ₁₂ : IR+[ γ₁ , γ₂ ]) → IR+[ γ₁ , γ₃ ]
Γγγ        ∘IR+ Γ₁₂       = Γ₁₂
Γ₂₃        ∘IR+ Γγγ       = Γ₂₃
Γιι g      ∘IR+ Γιι f     = Γιι $ g C.∘ f
γ          ∘IR+ Γσγ Γfγ   = Γσγ $ λ a → γ ∘IR+ Γfγ a
γ          ∘IR+ Γδγ ΓFγ   = Γδγ $ λ g → γ ∘IR+ ΓFγ g
Γισ a Γιf  ∘IR+ Γιι g     = Γισ a $ Γιf ∘IR+ Γιι g
Γιδ g ΓιF  ∘IR+ Γιι f     = Γιδ g $ ΓιF ∘IR+ Γιι f
Γσγ Γfγ    ∘IR+ Γισ a Γιf = Γfγ a ∘IR+ Γιf
Γσγ Γfγ    ∘IR+ Γδσ b ΓFf = Γδγ $ λ g → Γfγ b ∘IR+ ΓFf g
Γδγ ΓFγ    ∘IR+ Γιδ g ΓιF = ΓFγ (⊥-elim ∘ g) ∘IR+ ΓιF
Γδγ ΓFγ    ∘IR+ Γδδ g ΓFG = Γδγ $ λ f → ΓFγ (f ∘ g) ∘IR+ ΓFG f
Γδσ b ΓFf  ∘IR+ Γιδ g ΓιF = Γισ b $ ΓFf (⊥-elim ∘ g) ∘IR+ ΓιF
Γδσ b ΓFf  ∘IR+ Γδδ g ΓFG = Γδσ b $ λ f → ΓFf (f ∘ g) ∘IR+ ΓFG f
Γδδ g ΓFG  ∘IR+ Γιδ f ΓιF = Γιδ (f ∘ g) $ ΓFG (⊥-elim ∘ f) ∘IR+ ΓιF
Γδδ g ΓGH  ∘IR+ Γδδ f ΓFG = Γδδ (f ∘ g) $ λ h → ΓGH (h ∘ f) ∘IR+ ΓFG h

Γδι : {ℓ : Level} {A : Set ℓ} {F : (A → Obj) → IR+ ℓ} {F→ : [ F ]→} {c : Obj} ->
      ((g : A → Obj) -> IR+[ F g , ι c ]) -> IR+[ δ A F F→ , ι c ]
Γδι r = Γδγ r

-- Fam C and Fam C morphisms, plus coproduct stuff for Fam C -----

record FamC (ℓ : Level) : Set (suc ℓ ⊔ o) where
  constructor _,_
  field
    idx : Set ℓ
    fam : idx -> Obj
open FamC

ΣFamC : {ℓ : Level} (A : Set ℓ) -> (A -> FamC ℓ) -> FamC ℓ
ΣFamC A B = (Σ A (idx ∘ B)) , (λ { (a , b) → fam (B a) b })

record HomFamC {ℓ : Level} (A B : FamC ℓ) : Set (ℓ ⊔ m) where
  constructor _,_
  field
    idxfun : idx A -> idx B
    famfun : (x : idx A) -> fam A x ⇒ fam B (idxfun x)
open HomFamC

idFamC : {ℓ : Level} {A : FamC ℓ} -> HomFamC A A
idFamC = id , λ _ → C.id

_∘FamC_ : ∀ {ℓ : Level} {a b c : FamC ℓ} -> HomFamC b c -> HomFamC a b -> HomFamC a c
(h , k) ∘FamC (h' , k') = (h ∘ h') , (λ x → k (h' x) C.∘ k' x)

inA : {ℓ : Level} {A : Set ℓ} {B : A → FamC ℓ} (a : A) → HomFamC (B a) (ΣFamC A B)
inA a = _,_ a , λ _ → C.id

outΣ : {ℓ : Level} (A : Set ℓ) {B : A → FamC ℓ} {C : FamC ℓ}
       (p : (a : A) → HomFamC (B a) C) → HomFamC (ΣFamC A B) C
outΣ A p = uncurry (idxfun ∘ p) , uncurry (famfun ∘ p)

syntax outΣ A (λ a → p) = [ p ][ a ∈ A ]


------------------------------------------------------------------
-- Decoding ------------------------------------------------------
-- Object part

⟦_⟧IR+ : {ℓ : Level} (γ : IR+ ℓ) → FamC ℓ → FamC ℓ
⟦ ι c     ⟧IR+ UT      = Lift ⊤ , const c
⟦ σ A f   ⟧IR+ UT      = ΣFamC A $ λ a → ⟦ f a ⟧IR+ UT
⟦ δ A F _ ⟧IR+ (U , T) = ΣFamC (A → U) $ λ g → ⟦ F (T ∘ g) ⟧IR+ (U , T)

-- Morphism part


mutual
  -- not really mutual, ⟦_⟧Hom does not depend on ⟦_⟧→ ...
  -- However, if one considers ⟦_⟧IR+ and ⟦_⟧→ to be defined together
  -- (object and morphism part of the same functor), then there really
  -- is a mutual dependency.

  ⟦_⟧→ : {ℓ : Level} (γ : IR+ ℓ) {A B : FamC ℓ} (hk : HomFamC A B) →
        HomFamC (⟦ γ ⟧IR+ A) (⟦ γ ⟧IR+ B)
  ⟦ ι c      ⟧→ hk = idFamC
  ⟦ σ A f    ⟧→ hk = [ inA a ∘FamC (⟦ f a ⟧→ hk) ][ a ∈ A ]
  ⟦ δ A F F→ ⟧→ {X , P} {Y , Q} (h , k)
     = [ inA {B = λ g → ⟦ F (Q ∘ g) ⟧IR+ (Y , Q)} (h ∘ g)
          ∘FamC (⟦ F→ (k ∘ g) ⟧Hom (Y , Q)
          ∘FamC ⟦ F (P ∘ g) ⟧→ (h , k)) ][ g ∈ _ ]

  ⟦_⟧Hom : {ℓ : Level} {γ γ' : IR+ ℓ} (Γ : IR+[ γ , γ' ]) (UT : FamC ℓ) →
           HomFamC (⟦ γ ⟧IR+ UT) (⟦ γ' ⟧IR+ UT)
  ⟦ Γιι g ⟧Hom UT = id , (λ _ → g)
  ⟦ Γισ a r ⟧Hom UT = inA a ∘FamC (⟦ r ⟧Hom UT)
  ⟦ Γιδ {c} {A} {F} {F→} g r ⟧Hom (U , T)
   =      inA {B = λ g → ⟦ F (T ∘ g) ⟧IR+ (U , T)} (⊥-elim ∘ g)
    -- workaround for T ∘ ⊥-elim {U} = ⊥-elim {C},if this was
    -- definitional the following line would not be needed
    ∘FamC (⟦ F→ (λ a → ⊥-elim (g a)) ⟧Hom (U , T) 
    ∘FamC ⟦ r ⟧Hom (U , T))
  ⟦ Γσγ p ⟧Hom UT = [ ⟦ p a ⟧Hom UT ][ a ∈ _ ]
  ⟦ Γδσ a r ⟧Hom (U , T) = inA a ∘FamC [ ⟦ r (T ∘ g) ⟧Hom (U , T) ][ g ∈ _ ]
  ⟦ Γδδ {A} {F} {F→} {B} {G} f r ⟧Hom (U , T) = [ inA {B = λ g → ⟦ G (T ∘ g) ⟧IR+ (U , T)} (g ∘ f) ∘FamC ⟦ r (T ∘ g) ⟧Hom (U , T) ][ g ∈ (A -> U) ]
  ⟦ Γδγ p ⟧Hom (U , T) = [ ⟦ p (T ∘ h) ⟧Hom (U , T) ][ h ∈ _ ] 
  ⟦ Γγγ ⟧Hom UT = idFamC

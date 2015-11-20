module tt.typ.sub where


open import Data.Nat
open import Data.Fin as Fin hiding (_<_)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Function
open import Relation.Binary.PropositionalEquality as PEq using (_≡_ ; subst ; subst₂ ; cong ; cong₂)

open import tt.raw
open import tt.env
open import tt.sem
open import tt.sem.idS
open import tt.sem.rel
open import tt.sem.fus
open import tt.typ
import tt.typ.ren as REN


module TypingSubst
       (_↝_ : {n : ℕ} (a b : Type n) → Set)
       (weak↝ : {m n : ℕ} {a b : Type m} (inc : m ⊆ n) → a ↝ b → weakT inc a ↝ weakT inc b)
       (subst↝ : {m n : ℕ} {a b : Type m} (ρ : Var m =>[ Infer ] n) → a ↝ b → substT a ρ ↝ substT b ρ)
       where

  open Typing _↝_
  module Sub = Semantics Substitution

  infix 1 [_]_⇒_
  record [_]_⇒_ {m n : ℕ} (ρ : Var m =>[ Infer ] n) (Γ : Context m) (Δ : Context n) : Set where
    constructor pack
    field substVar : {k : Fin m} {A : Type m} → Γ ⊢var k ∈ A → Δ ⊢ lookup ρ k ∈ substT A ρ
  open [_]_⇒_

  Lift : {m n : ℕ} {ρ : Var m =>[ Infer ] n} {Γ : Context m} {Δ : Context n} {A : Type m} →
         (sub : [ ρ ] Γ ⇒ Δ) → [ Sub.lift ρ ] Γ ∙⟩ A ⇒ Δ ∙⟩ substT A ρ
  substVar (Lift {ρ = ρ} {Δ = Δ} {A} sub) zro     =

    let eq : weakT extend (substT A ρ) ≡ substT (weakT extend A) (Sub.lift ρ)
        eq = PEq.trans (fusion.lemmaT SubRen A (λ _ → PEq.refl))
             $ PEq.sym (fusion.lemmaT RenSub A (λ _ → PEq.refl))
        
    in subst (Δ ∙⟩ substT A ρ ⊢ `var zero ∈_) eq (`var zro)
   
  substVar (Lift {ρ = ρ} {Δ = Δ} sub) (suc {A = A} {B} {k = k} Hk) =

    let eq : weakT extend (substT B ρ) ≡ substT (weakT extend B) (Sub.lift ρ)
        eq = PEq.trans (fusion.lemmaT SubRen B (λ _ → PEq.refl))
             $ PEq.sym (fusion.lemmaT RenSub B (λ _ → PEq.refl))

        wkK : Δ ∙⟩ substT A ρ ⊢ weakI extend (lookup ρ k) ∈ weakT extend (substT B ρ)
        wkK = let open REN.TypingWeak _↝_ weak↝ in weak∈ extend REN.EXTEND (substVar sub Hk)
        
    in subst (Δ ∙⟩ substT A ρ ⊢ lookup (Sub.lift ρ) (suc k) ∈_) eq wkK

  substI-comm : {m n : ℕ} (ρ : Var m =>[ Infer ] n) (i : Infer m) →
                ∀[_] {Infer} {Infer} _≡_
                  (pack (λ k → substI (lookup (Sub.lift ρ) k) (Sub.⟦diag⟧ ∙ substI i ρ)))
                  (pack (λ k → substI (lookup (Sub.⟦diag⟧ ∙ i) k) ρ))
  substI-comm ρ i zero    = PEq.refl
  substI-comm ρ i (suc k) = PEq.trans (fusion.lemmaI RenSub (lookup ρ k) (λ _ → PEq.refl)) $
                            identity.lemmaI SubId (lookup ρ k)


  subst∈ : {m n : ℕ} {Γ : Context m} {Δ : Context n} {i : Infer m} {A : Type m}
           (ρ : Var m =>[ Infer ] n) (sub : [ ρ ] Γ ⇒ Δ) (t : Γ ⊢ i ∈ A) → Δ ⊢ substI i ρ ∈ substT A ρ
  substSet : {m n : ℕ} {Γ : Context m} {Δ : Context n} {ℓ : ℕ} {A : Type m}
             (ρ : Var m =>[ Infer ] n) (sub : [ ρ ] Γ ⇒ Δ) → Γ ⊢set ℓ ∋ A → Δ ⊢set ℓ ∋ substT A ρ
  subst∋ : {m n : ℕ} {Γ : Context m} {Δ : Context n} {c : Check m} {A : Type m}
           (ρ : Var m =>[ Infer ] n) (sub : [ ρ ] Γ ⇒ Δ) → Γ ⊢ A ∋ c → Δ ⊢ substT A ρ ∋ substC c ρ

  subst∈ ρ sub (`var k)   = substVar sub k
  subst∈ ρ sub (`ann Ht)  = `ann (subst∋ ρ sub Ht)
  subst∈ ρ sub (`app {f} {t} {A} {B} Hf Ht) =

    let ih : _ ⊢ `app (substI f ρ) (substC t ρ) ∈ Substitution ⊨ substT B (Sub.lift ρ) ⟨ substI (`ann t A) ρ /0⟩T
        ih = `app (subst∈ ρ sub Hf) (subst∋ ρ sub Ht)

        eq : Substitution ⊨ substT B (Sub.lift ρ) ⟨ substI (`ann t A) ρ /0⟩T
           ≡ substT (Substitution ⊨  B ⟨ `ann t A /0⟩T) ρ
        eq = PEq.trans (fusion.lemmaT SubSub B (substI-comm ρ (`ann t A)))
             $ PEq.sym (fusion.lemmaT SubSub B (λ _ → PEq.refl))

    in subst (_ ⊢ `app (substI f ρ) (substC t ρ) ∈_) eq ih

  subst∈ ρ sub (`fst t)       = `fst (subst∈ ρ sub t)
  subst∈ ρ sub (`snd {t} {A} {B} Ht)       =

    let ih : _ ⊢ `snd (substI t ρ) ∈ Substitution ⊨ substT B (Sub.lift ρ) ⟨ substI (`fst t) ρ /0⟩T
        ih = `snd (subst∈ ρ sub Ht)

        eq : Substitution ⊨ substT B (Sub.lift ρ) ⟨ substI (`fst t) ρ /0⟩T
           ≡ substT (Substitution ⊨ B ⟨ `fst t /0⟩T) ρ
        eq = PEq.trans (fusion.lemmaT SubSub B (substI-comm ρ (`fst t)))
             $ PEq.sym (fusion.lemmaT SubSub B (λ _ → PEq.refl))

    in subst (_ ⊢ `snd (substI t ρ) ∈_) eq ih

  subst∈ {Δ = Δ} ρ sub (`ind {p} {z} {s} {m} {ℓ} Hp Hz Hs Hm) =

    let pTy : {n : ℕ} → Type n
        pTy = λ {n} → `pi `nat (`set ℓ)

        ihS : Δ ⊢ substT (`pi `nat (appT (weakC extend p) pTy var₀
                                 `→ appT (weakC extend p) pTy (`suc var₀)))
                  ρ ∋ substC s ρ
        ihS = subst∋ ρ sub Hs

        subS : Δ ⊢ `pi `nat (appT (weakC extend (substC p ρ)) pTy var₀
                          `→ appT (weakC extend (substC p ρ)) pTy (`suc var₀))
                 ∋ substC s ρ
        subS =
          let patt = λ u vw → `pi `nat (`pi (appT u pTy var₀) (appT (proj₁ vw) pTy (`suc (proj₂ vw))))

              eq₁  : substC (weakC extend p) (Sub.lift ρ) ≡ weakC extend (substC p ρ)
              eq₁ = PEq.trans (fusion.lemmaC RenSub p (λ _ → PEq.refl))
                    $ PEq.sym (fusion.lemmaC SubRen p (λ _ → PEq.refl))

              eq₂ : substC (weakC extend $ weakC extend p) (Sub.lift (Sub.lift ρ))
                  ≡ weakC extend (weakC extend (substC p ρ))
              eq₂ = PEq.trans (fusion.lemmaC RenSub (weakC extend p) (λ _ → PEq.refl)) $
                    PEq.trans (fusion.lemmaC RenSub p (λ _ → PEq.refl)) $ PEq.sym $
                    PEq.trans (fusion.lemmaC RenRen (substC p ρ) (λ _ → PEq.refl)) $
                    fusion.lemmaC SubRen p (λ k → PEq.sym $ fusion.lemmaI RenRen (lookup ρ k) (λ _ → PEq.refl))

              eq₃ : substC (weakC extend var₀) (Sub.lift $ Sub.lift ρ) ≡ weakC extend var₀
              eq₃ = fusion.lemmaC RenSub var₀ {extend} {Sub.lift $ Sub.lift ρ} (λ _ → PEq.refl)

          in subst (Δ ⊢_∋ substC s ρ) (cong₂ patt eq₁ $ cong₂ _,_ eq₂ eq₃) ihS

    in `ind (subst∋ ρ sub Hp) (subst∋ ρ sub Hz) subS (subst∈ ρ sub Hm)

  subst∈ ρ sub (`red red t)   = `red (subst↝ ρ red) (subst∈ ρ sub t)


  substSet ρ sub (`sig A B) = `sig (substSet ρ sub A) (substSet (Sub.lift ρ) (Lift sub) B)
  substSet ρ sub (`pi A B)  = `pi (substSet ρ sub A) (substSet (Sub.lift ρ) (Lift sub) B)
  substSet ρ sub `nat       = `nat
  substSet ρ sub (`set ℓ)   = `set ℓ
  substSet ρ sub (`elt e)   = `elt (subst∈ ρ sub e)


  subst∋ ρ sub (`lam e)     = `lam (subst∋ (wk[ weakI ] extend ρ ∙ Sub.fresh) (Lift sub) e)
  subst∋ {Δ = Δ} ρ sub (`per {a} {b} {A} {B} Ha Hb) =

    let eq : substT (Substitution ⊨ B ⟨ `ann a A /0⟩T) ρ
           ≡ Substitution ⊨ substT B (Sub.lift ρ) ⟨ substI (`ann a A) ρ /0⟩T
        eq = PEq.trans (fusion.lemmaT SubSub B (λ _ → PEq.refl))
             $ PEq.sym (fusion.lemmaT SubSub B (substI-comm ρ (`ann a A)))
        
    in `per (subst∋ ρ sub Ha) (subst (Δ ⊢_∋ substC b ρ) eq (subst∋ ρ sub Hb))
    
  subst∋ ρ sub `zro         = `zro
  subst∋ ρ sub (`suc m)     = `suc (subst∋ ρ sub m)
  subst∋ ρ sub (`emb e)     = `emb (subst∈ ρ sub e)
  subst∋ ρ sub (`typ A)     = `typ (substSet ρ sub A)
  subst∋ ρ sub (`red red t) = `red (subst↝ ρ red) (subst∋ ρ sub t)

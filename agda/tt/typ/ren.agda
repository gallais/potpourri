module tt.typ.ren where


open import Data.Nat
open import Data.Fin as Fin hiding (_<_)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Function
open import Relation.Binary.PropositionalEquality as PEq using (_≡_ ; subst ; cong ; cong₂)

open import tt.raw
open import tt.env
open import tt.sem
open import tt.sem.idS
open import tt.sem.rel
open import tt.sem.fus
open import tt.typ

infix 1 [_]_⇒_
record [_]_⇒_ {m n : ℕ} (inc : m ⊆ n) (Γ : Context m) (Δ : Context n) : Set where
  constructor pack
  field weakVar : {k : Fin m} {A : Type m} → Γ ⊢var k ∈ A → Δ ⊢var lookup inc k ∈ weakT inc A
open [_]_⇒_ public

REFL : {m : ℕ} {Γ : Context m} → [ refl ] Γ ⇒ Γ
weakVar (REFL {Γ = Γ}) {k} {A} Hk = subst (Γ ⊢var k ∈_) (PEq.sym $ identity.lemmaT RenId A) Hk

STEP : {m n : ℕ} {inc : m ⊆ n} {Γ : Context m} {Δ : Context n} →
       [ inc ] Γ ⇒ Δ → (A : Type m) → [ step inc ] Γ ⇒ (Δ ∙⟩ weakT inc A)
weakVar (STEP {inc = inc} {Δ = Δ} ren A) {k} {B} Hk =

  let eq : weakT extend (weakT inc B) ≡ weakT (step inc) B
      eq = fusion.lemmaT RenRen B (λ _ → PEq.refl)

  in subst (Δ ∙⟩ weakT inc A ⊢var lookup (step inc) k ∈_) eq (suc (weakVar ren Hk))

EXTEND : {m : ℕ} {Γ : Context m} {A : Type m} → [ extend ] Γ ⇒ Γ ∙⟩ A
EXTEND {Γ = Γ} {A = A} = subst (λ A → [ extend ] Γ ⇒ Γ ∙⟩ A) (identity.lemmaT RenId A) $ STEP REFL A

POP! : {m n : ℕ} {inc : m ⊆ n} {Γ : Context m} {Δ : Context n} →
       [ inc ] Γ ⇒ Δ → (A : Type m) → [ pop! inc ] Γ ∙⟩ A ⇒ (Δ ∙⟩ weakT inc A)
weakVar (POP! {inc = inc} {Δ = Δ} ren A) zro =

  let eq : weakT extend (weakT inc A)
         ≡ weakT (pop! inc) (weakT extend A)
      eq = PEq.trans (fusion.lemmaT RenRen A (λ _ → PEq.refl))
         $ PEq.sym $ fusion.lemmaT RenRen A (λ _ → PEq.refl)

  in subst (Δ ∙⟩ weakT inc A ⊢var zero ∈_) eq zro

weakVar (POP! {inc = inc} {Δ = Δ} ren A) (suc {B = B} {k} Hk) =
  
  let ih : Δ ∙⟩ weakT inc A ⊢var lookup (pop! inc) (suc k) ∈ weakT extend (weakT inc B)
      ih = suc (weakVar ren Hk)

      eq : weakT extend (weakT inc B)
         ≡ weakT (pop! inc) (weakT extend B)
      eq = PEq.trans (fusion.lemmaT RenRen B (λ _ → PEq.refl))
         $ PEq.sym $  fusion.lemmaT RenRen B (λ _ → PEq.refl)
        
  in subst (Δ ∙⟩ weakT inc A ⊢var lookup (pop! inc) (suc k) ∈_) eq ih


weakβT : {m n : ℕ} (t : Type (suc m)) (u : Infer m) (m⊆n : m ⊆ n) →
         Substitution ⊨ weakT (pop! m⊆n) t ⟨ weakI m⊆n u /0⟩T
         ≡ weakT m⊆n (Substitution ⊨ t ⟨ u /0⟩T)
weakβT {m} {n} t u m⊆n = PEq.trans eq₁ $ PEq.sym eq₂ where

  eq₁ : Substitution ⊨ weakT (pop! m⊆n) t ⟨ weakI m⊆n u /0⟩T
      ≡ Substitution ⊨⟦ t ⟧T (trans m⊆n (pack `var) ∙ weakI m⊆n u)
  eq₁ = fusion.lemmaT RenSub t $ λ { zero → PEq.refl ; (suc k) → PEq.refl }

  eq₂ : weakT m⊆n (Substitution ⊨ t ⟨ u /0⟩T)
      ≡ Substitution ⊨⟦ t ⟧T (trans m⊆n (pack `var) ∙ weakI m⊆n u)
  eq₂ = fusion.lemmaT SubRen t $ λ { zero → PEq.refl ; (suc k) → PEq.refl }

module TypingWeak
       (_↝_ : {n : ℕ} (a b : Type n) → Set)
       (weak↝ : {m n : ℕ} {a b : Type m} (inc : m ⊆ n) → a ↝ b → weakT inc a ↝ weakT inc b)
       where

  open Typing _↝_

  weak∈ : {m n : ℕ} {Γ : Context m} {Δ : Context n} {i : Infer m} {A : Type m}
          (m⊆n : m ⊆ n) (ren : [ m⊆n ] Γ ⇒ Δ) (t : Γ ⊢ i ∈ A) → Δ ⊢ weakI m⊆n i ∈ weakT m⊆n A
  weakSet : {m n : ℕ} {Γ : Context m} {Δ : Context n} {ℓ : ℕ} {A : Type m}
            (m⊆n : m ⊆ n) (ren : [ m⊆n ] Γ ⇒ Δ) → Γ ⊢set ℓ ∋ A → Δ ⊢set ℓ ∋ weakT m⊆n A
  weak∋ : {m n : ℕ} {Γ : Context m} {Δ : Context n} {c : Check m} {A : Type m}
          (m⊆n : m ⊆ n) (ren : [ m⊆n ] Γ ⇒ Δ) → Γ ⊢ A ∋ c → Δ ⊢ weakT m⊆n A ∋ weakC m⊆n c


  weak∈ m⊆n ren (`var v)       = `var (weakVar ren v)
  weak∈ m⊆n ren (`ann t)       = `ann (weak∋ m⊆n ren t)
  weak∈ m⊆n ren (`fst t)       = `fst (weak∈ m⊆n ren t)
  weak∈ {n = n} {Δ = Δ} m⊆n ren (`ind {p} {z} {s} {m} {ℓ} Hp Hz Hs Hm) =
    
    let pTy : {n : ℕ} → Type n
        pTy = λ {n} → `pi `nat (`set ℓ)
        ihS : Δ ⊢ weakT m⊆n (`pi `nat (appT (weakC extend p) pTy var₀
                                    `→ appT (weakC extend p) pTy (`suc var₀)))
                ∋ weakC m⊆n s
        ihS = weak∋ m⊆n ren Hs

        wkS : Δ ⊢ `pi `nat (appT (weakC extend (weakC m⊆n p)) pTy var₀
                         `→ appT (weakC extend (weakC m⊆n p)) pTy (`suc var₀))
              ∋ weakC m⊆n s
        wkS = let patt = λ u vw → `pi `nat (`pi (appT u pTy var₀) (appT (proj₁ vw) pTy (`suc (proj₂ vw))))

                  ↑    = Semantics.lift Renaming

                  eq₁ : weakC (↑ m⊆n) (weakC extend p) ≡ weakC extend (weakC m⊆n p)
                  eq₁ = PEq.trans (fusion.lemmaC RenRen p (λ _ → PEq.refl))
                       $ PEq.sym $ fusion.lemmaC RenRen p (λ _ → PEq.refl)

                  eq₂ : weakC (↑ (↑ m⊆n)) (weakC extend (weakC extend p))
                      ≡ weakC extend (weakC extend $ weakC m⊆n p)
                  eq₂ = PEq.trans (fusion.lemmaC RenRen (weakC extend p) (λ _ → PEq.refl)) $
                        PEq.trans (fusion.lemmaC RenRen p (λ _ → PEq.refl)) $ PEq.sym $
                        PEq.trans (fusion.lemmaC RenRen (weakC m⊆n p) (λ _ → PEq.refl)) $
                        (fusion.lemmaC RenRen p (λ _ → PEq.refl))

                  eq₃ : weakC (↑ (↑ m⊆n)) (weakC extend var₀) ≡ weakC extend var₀
                  eq₃ = fusion.lemmaC RenRen var₀ {extend} {↑ (↑ m⊆n)} (λ _ → PEq.refl)

              in subst (Δ ⊢_∋ weakC m⊆n s) (cong₂ patt eq₁ $ cong₂ _,_ eq₂ eq₃) ihS

    in `ind (weak∋ m⊆n ren Hp) (weak∋ m⊆n ren Hz) wkS (weak∈ m⊆n ren Hm)

  weak∈ m⊆n ren (`red red t)   = `red (weak↝ m⊆n red) (weak∈ m⊆n ren t)
  weak∈ m⊆n ren (`snd {t} {A} {B} Ht)       =
    
    let ih  : _ ⊢ weakI m⊆n (`snd t) ∈ (Substitution ⊨ weakT _ B ⟨ weakI m⊆n (`fst t) /0⟩T)
        ih  = `snd (weak∈ m⊆n ren Ht)
    in subst (_ ⊢ weakI m⊆n (`snd t) ∈_) (weakβT B (`fst t) m⊆n) ih

  weak∈ m⊆n ren (`app {f} {t} {A} {B} Hf Ht) =
    
    let ih  : _ ⊢ weakI m⊆n (`app f t) ∈ Substitution ⊨ weakT _ B ⟨ weakI m⊆n (`ann t A) /0⟩T
        ih  = `app (weak∈ m⊆n ren Hf) (weak∋ m⊆n ren Ht)
          
    in subst (_ ⊢ weakI m⊆n (`app f t) ∈_) (weakβT B (`ann t A) m⊆n) ih



  weakSet m⊆n ren (`sig A B) = `sig (weakSet m⊆n ren A) $ weakSet (pop! m⊆n) (POP! ren _) B
  weakSet m⊆n ren (`pi A B)  = `pi (weakSet m⊆n ren A) $ weakSet (pop! m⊆n) (POP! ren _) B
  weakSet m⊆n ren `nat       = `nat
  weakSet m⊆n ren (`set ℓ)   = `set ℓ
  weakSet m⊆n ren (`elt e)   = `elt (weak∈ m⊆n ren e)



  weak∋ m⊆n ren (`lam b)     = `lam (weak∋ (pop! m⊆n) (POP! ren _) b)
  weak∋ m⊆n ren (`per {a} {b} {A} {B} Ha Hb)   =
    let ih  : _ ⊢ weakT m⊆n (Substitution ⊨ B ⟨ `ann a A /0⟩T) ∋ weakC m⊆n b
        ih  = weak∋ m⊆n ren Hb

    in `per (weak∋ m⊆n ren Ha) (subst (_ ⊢_∋ weakC m⊆n b) (PEq.sym $ weakβT B (`ann a A) m⊆n) ih)

  weak∋ m⊆n ren `zro         = `zro
  weak∋ m⊆n ren (`suc m)     = `suc (weak∋ m⊆n ren m)
  weak∋ m⊆n ren (`emb e)     = `emb (weak∈ m⊆n ren e)
  weak∋ m⊆n ren (`typ s)     = `typ (weakSet m⊆n ren s)
  weak∋ m⊆n ren (`red red t) = `red (weak↝ m⊆n red) (weak∋ m⊆n ren t)



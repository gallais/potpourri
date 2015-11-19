module tt.sem.idS where

open import Data.Nat
open import Data.Fin hiding (lift)
open import Data.Product using (_,_ ; proj₁ ; proj₂ ; uncurry)
open import Function

open import tt.raw
open import tt.env hiding (refl ; trans)
open import tt.sem
open import tt.sem.rel
open import Relation.Binary.PropositionalEquality

record Identity {E : ℕ → Set} (Syn : SyntacticSemantics E) : Set where

  open SyntacticSemantics Syn
  S = syntacticSemantics.lemma Syn
  module S = Semantics S
  
  field
    ⟦var⟧^R : {n : ℕ} (k : Fin n) → ⟦var⟧ (lookup S.⟦diag⟧ k) ≡ `var k
    ⟦wk⟧^R  : {n : ℕ} (k : Fin n) → ⟦wk⟧ extend (lookup S.⟦diag⟧ k) ≡ lookup S.⟦diag⟧ (suc k)


module identity {E : ℕ → Set} {Syn : SyntacticSemantics E} (Id : Identity Syn) where

  open Identity Id

  lemmaC : {m : ℕ} (t : Check m) → S ⊨⟦ t ⟧C S.⟦diag⟧ ≡ t
  lemmaT : {m : ℕ} (t : Type  m) → S ⊨⟦ t ⟧T S.⟦diag⟧ ≡ t
  lemmaI : {m : ℕ} (t : Infer m) → S ⊨⟦ t ⟧I S.⟦diag⟧ ≡ t


  lemmaC (`typ A)   = cong `typ (lemmaT A)
  lemmaC (`lam t)   =
  
    let eqt : S ⊨⟦ t ⟧C (S.weakE extend S.⟦diag⟧ ∙ S.fresh)
            ≡ S ⊨⟦ t ⟧C S.⟦diag⟧
        eqt = related.lemmaC (SynExt Syn) t (λ { zero → refl ; (suc k) → ⟦wk⟧^R k })

    in  cong `lam (trans eqt (lemmaC t))
    
  lemmaC (`per a b) = cong₂ `per (lemmaC a) (lemmaC b)
  lemmaC `zro       = refl
  lemmaC (`suc m)   = cong `suc (lemmaC m)
  lemmaC (`emb e)   = cong `emb (lemmaI e)

  lemmaT (`sig A B) =

    let eqB : S ⊨⟦ B ⟧T (S.weakE extend S.⟦diag⟧ ∙ S.fresh)
            ≡ S ⊨⟦ B ⟧T S.⟦diag⟧
        eqB = related.lemmaT (SynExt Syn) B (λ { zero → refl ; (suc k) → ⟦wk⟧^R k })

    in cong₂ `sig (lemmaT A) (trans eqB (lemmaT B))

  lemmaT (`pi A B)  =
  
    let eqB : S ⊨⟦ B ⟧T (S.weakE extend S.⟦diag⟧ ∙ S.fresh)
            ≡ S ⊨⟦ B ⟧T S.⟦diag⟧
        eqB = related.lemmaT (SynExt Syn) B (λ { zero → refl ; (suc k) → ⟦wk⟧^R k })

    in  cong₂ `pi (lemmaT A) (trans eqB (lemmaT B))
    
  lemmaT `nat       = refl
  lemmaT (`set ℓ)   = refl
  lemmaT (`elt e)   = cong `elt (lemmaI e)


  lemmaI (`var k)       = ⟦var⟧^R k
  lemmaI (`ann t A)     = cong₂ `ann (lemmaC t) (lemmaT A)
  lemmaI (`app t u)     = cong₂ `app (lemmaI t) (lemmaC u)
  lemmaI (`fst t)       = cong `fst (lemmaI t)
  lemmaI (`snd t)       = cong `snd (lemmaI t)
  lemmaI (`ind p z s t) = cong₂ (λ p → uncurry (`ind (proj₁ p) (proj₂ p)))
                                (cong₂ _,_ (lemmaC p) (lemmaC z)) (cong₂ _,_ (lemmaC s) (lemmaI t))



RenId : Identity SyntacticRenaming
RenId = record { ⟦var⟧^R = λ _ → refl ; ⟦wk⟧^R = λ _ → refl }


SubId : Identity SyntacticRenaming
SubId = record { ⟦var⟧^R = λ k → identity.lemmaI RenId (`var k) ; ⟦wk⟧^R = λ _ → refl }

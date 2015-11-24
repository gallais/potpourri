module tt.typ.dec where

open import Data.Nat
open import Data.Fin
open import Data.Product
open import Function
open import Relation.Nullary

open import tt.raw
open import tt.red
open import tt.env
open import tt.sem
open import tt.typ
open import tt.typ.inv

module typeCheck
       (_↝_        : {n : ℕ} (t u : Type n) → Set)
       (eltAnn↝    : {n : ℕ} {A B : Type n} {ℓ : ℕ} → `elt (`ann (`typ A) B) [ _↝_ ⟩* A)
       (whnf       : {n : ℕ} → Type n → Type n)
       (whnfCon    : {n : ℕ} (t : Type n) → Type whnf t ≡^Con whnf t)
       (whnfReduct : {n : ℕ} (t : Type n) → t [ _↝_ ⟩* whnf t)
       (whnfSpec   : {n : ℕ} (t : Type n) →
                     (ex : ∃ λ s → (t [ _↝_ ⟩* s) × Type s ≡^Con s) →
                     Type whnf t ≡^Con proj₁ ex)
       where

  open Typing _↝_
  open TypingInversion _↝_

  -- Type Inference for variables is total: it's a simple lookup
  -- in the context!

  typeInferVar : {n : ℕ} (Γ : Context n) (k : Fin n) → ∃ λ A → Γ ⊢var k ∈ A
  typeInferVar (_ ∙⟩ A) zero    = , zro
  typeInferVar (Γ ∙⟩ _) (suc k) = map (weakT extend) suc $ typeInferVar Γ k

  -- The decidability of Type Checking and Type Inference can then be
  -- proven by a mutual induction

  typeType : {n : ℕ} (Γ : Context n) (ℓ : ℕ) (A : Type n) → Dec (Γ ⊢set ℓ ∋ A)
  typeCheck : {n : ℕ} (Γ : Context n) (A : Type n) (a : Check n) → Dec (Γ ⊢ A ∋ a)
  typeInfer : {n : ℕ} (Γ : Context n) (e : Infer n) → Dec (∃ λ A → Γ ⊢ e ∈ A)


  typeType Γ ℓ (`sig A B) with typeType Γ ℓ A | typeType (Γ ∙⟩ A) ℓ B
  ... | yes hA | yes hB = yes (`sig hA hB)
  ... | no ¬hA | _      = no (¬hA ∘ proj₁ ∘ Γ⊢set∋ΣAB-inv)
  ... | yes hA | no ¬hB = no (¬hB ∘ proj₂ ∘ Γ⊢set∋ΣAB-inv)

  typeType Γ ℓ (`pi A B)  with typeType Γ ℓ A | typeType (Γ ∙⟩ A) ℓ B
  ... | yes hA | yes hB = yes (`pi hA hB)
  ... | no ¬hA | _      = no (¬hA ∘ proj₁ ∘ Γ⊢set∋ΠAB-inv)
  ... | yes hA | no ¬hB = no (¬hB ∘ proj₂ ∘ Γ⊢set∋ΠAB-inv)
  
  typeType Γ 0       `nat = yes `nat
  typeType Γ (suc ℓ) `nat = no λ ()
  
  typeType Γ ℓ (`set ℓ′) with suc ℓ′ ≤? ℓ
  ... | yes lt = yes (`set lt)
  ... | no ¬lt = no (¬lt ∘ Γ⊢set∋set-inv)
  
  typeType Γ ℓ (`elt e) with typeInfer Γ e
  ... | yes (A , hA) with whnf A | whnfReduct A | whnfSpec A
  ... | `set ℓ′ | A↝*setℓ′ | spec with ℓ ≟ ℓ′
  ... | yes p rewrite p = yes (`elt (reduceInfer A↝*setℓ′ hA))
  ... | no ¬p = no {!!}
  typeType Γ ℓ (`elt e) | yes (A , hA) | `sig _ _ | _ | spec = no (λ p → case spec (, {!!} , `set _) of λ ())
  typeType Γ ℓ (`elt e) | yes (A , hA) | `pi _ _  | _ | spec = {!!}
  typeType Γ ℓ (`elt e) | yes (A , hA) | `nat     | _ | spec = {!!}
  typeType Γ ℓ (`elt e) | yes (A , hA) | `elt _   | _ | spec = {!!}
  typeType Γ ℓ (`elt e) | no ¬p = no (¬p ∘ Γ⊢set∋elt-inv)


  -- TYPE CHEKING

  typeCheck Γ A (`typ B) with whnf A | whnfReduct A | whnfSpec A
  ... | `set ℓ | A↝*set | _ with typeType Γ ℓ B
  ... | yes p = yes (expandCheck A↝*set (`typ p))
  ... | no ¬p = no {!!}
  
  typeCheck Γ A (`typ B) | `sig _ _ | _ | spec = no (λ p → case spec (, proj₂ (Γ⊢A∋typ-inv p) , `set _) of λ ())
  typeCheck Γ A (`typ B) | `pi _ _  | _ | spec = no (λ p → case spec (, proj₂ (Γ⊢A∋typ-inv p) , `set _) of λ ())
  typeCheck Γ A (`typ B) | `nat     | _ | spec = no (λ p → case spec (, proj₂ (Γ⊢A∋typ-inv p) , `set _) of λ ())
  typeCheck Γ A (`typ B) | `elt _   | _ | spec = no (λ p → case spec (, proj₂ (Γ⊢A∋typ-inv p) , `set _) of λ ())


  typeCheck Γ A (`lam b) with whnf A | whnfReduct A | whnfSpec A
  ... | `pi S T | A↝*ΠST | _ with typeCheck (Γ ∙⟩ S) T b
  ... | yes p = yes (expandCheck A↝*ΠST (`lam p))
  ... | no ¬p = no {!!}

  typeCheck Γ A (`lam b) | `sig _ _ | _ | spec = no (λ p → case spec (, proj₂ (Γ⊢A∋λb-inv p) , `pi) of λ ())
  typeCheck Γ A (`lam b) | `nat     | _ | spec = no (λ p → case spec (, proj₂ (Γ⊢A∋λb-inv p) , `pi) of λ ())
  typeCheck Γ A (`lam b) | `set _   | _ | spec = no (λ p → case spec (, proj₂ (Γ⊢A∋λb-inv p) , `pi) of λ ())
  typeCheck Γ A (`lam b) | `elt _   | _ | spec = no (λ p → case spec (, proj₂ (Γ⊢A∋λb-inv p) , `pi) of λ ())


  typeCheck Γ A (`per a b) with whnf A | whnfReduct A | whnfSpec A
  ... | `sig S T | A↝*ΣST | _ with typeCheck Γ S a | typeCheck Γ (Substitution ⊨ T ⟨ `ann a S /0⟩T) b
  ... | yes p₁ | yes p₂ = yes (expandCheck A↝*ΣST (`per p₁ p₂))
  ... | no ¬p₁ | _      = no {!!}
  ... | yes p₁ | no ¬p₂ = no {!!}

  typeCheck Γ A (`per a b) | `pi _ _ | _ | sp = no (λ p → case sp (, proj₂ (Γ⊢A∋a,b-inv p) , `sig) of λ ())
  typeCheck Γ A (`per a b) | `nat  | _ | sp = no (λ p → case sp (, proj₂ (Γ⊢A∋a,b-inv p) , `sig) of λ ())
  typeCheck Γ A (`per a b) | `set _ | _ | sp = no (λ p → case sp (, proj₂ (Γ⊢A∋a,b-inv p) , `sig) of λ ())
  typeCheck Γ A (`per a b) | `elt _ | _ | sp = no (λ p → case sp (, proj₂ (Γ⊢A∋a,b-inv p) , `sig) of λ ())


  typeCheck Γ A `zro with whnf A | whnfReduct A | whnfSpec A
  ... | `nat    | A↝*ℕ  | _ = yes (expandCheck A↝*ℕ `zro)
  ... | `sig _ _  | A↝*ty | spec = no (λ p → case spec (`nat , Γ⊢A∋0-inv p , `nat) of (λ ()))
  ... | `pi  _ _  | A↝*ty | spec = no (λ p → case spec (`nat , Γ⊢A∋0-inv p , `nat) of (λ ()))
  ... | `set _  | A↝*ty | spec = no (λ p → case spec (`nat , Γ⊢A∋0-inv p , `nat) of (λ ()))
  ... | `elt _ | A↝*ty | spec = no (λ p → case spec (`nat , Γ⊢A∋0-inv p , `nat) of (λ ()))


  typeCheck Γ A (`suc a) with whnf A | whnfReduct A | whnfSpec A
  ... | `nat   | A↝*ℕ  | _ with typeCheck Γ `nat a
  ... | yes p = yes (expandCheck A↝*ℕ (`suc p))
  ... | no ¬p = no (¬p ∘ Γ⊢A∋Sm-inv′)
  typeCheck Γ A (`suc a) | `sig _ _  | A↝*ty | spec = no (λ p → case spec (, Γ⊢A∋Sm-inv p , `nat) of (λ ()))
  typeCheck Γ A (`suc a) | `pi  _ _  | A↝*ty | spec = no (λ p → case spec (, Γ⊢A∋Sm-inv p , `nat) of (λ ()))
  typeCheck Γ A (`suc a) | `set _  | A↝*ty | spec = no (λ p → case spec (, Γ⊢A∋Sm-inv p , `nat) of (λ ()))
  typeCheck Γ A (`suc a) | `elt _  | A↝*ty | spec = no (λ p → case spec (, Γ⊢A∋Sm-inv p , `nat) of (λ ()))



  typeCheck Γ A (`emb e) with typeInfer Γ e
  ... | yes p = {!!}
  ... | no ¬p = no (¬p ∘ Γ⊢A∋emb-inv)


  -- TYPE INFERENCE


  -- Γ ⊢ `var k ∈ Γ ‼ k
  typeInfer Γ (`var k)   = yes $ map id `var $ typeInferVar Γ k

  -- Γ ⊢ A ∋ t
  -------------------------------
  -- Γ ⊢ `ann t A ∈ A
  typeInfer Γ (`ann t A) with typeCheck Γ A t
  ... | yes p = yes (A , `ann p)
  ... | no ¬p = no (¬p ∘ Γ⊢anntA∈A-inv ∘ proj₂)

  -- Γ ⊢ e ∈ A    A ↝* `pi S T   Γ ⊢ S ∋ u
  -----------------------------------------
  -- Γ ⊢ `app e u ∈ T ⟨ u /0⟩
  typeInfer Γ (`app e u) with typeInfer Γ e
  ... | no ¬p = no (¬p ∘ Γ⊢appeu∈T-inv ∘ proj₂)
  ... | yes (A , Γ⊢e∈A) with whnf A | whnfReduct A | whnfSpec A
  ... | `pi S T | A↝*ΠST | _ with typeCheck Γ S u
  ... | yes prf = yes (Substitution ⊨ T ⟨ `ann u S /0⟩T , `app (reduceInfer A↝*ΠST Γ⊢e∈A) prf)
  ... | no ầejgt = no {!!}


  typeInfer Γ (`app e u) | yes (A , e∈A) | `sig _ _  | _ | spec = no (λ p → case spec (, {!!} , `pi) of λ ())
  typeInfer Γ (`app e u) | yes (A , e∈A) | `nat      | _ | spec = {!!}
  typeInfer Γ (`app e u) | yes (A , e∈A) | `set _    | _ | spec = {!!}
  typeInfer Γ (`app e u) | yes (A , e∈A) | `elt _    | _ | spec = {!!}


  typeInfer Γ (`fst e) with typeInfer Γ e
  ... | yes (A , Γ⊢e∈A) with whnf A | whnfReduct A | whnfSpec A
  ... | `sig S T | A↝*ΣST | _ = yes (S , `fst (reduceInfer A↝*ΣST Γ⊢e∈A))
  ... |  _  | _ | spec =  {!!}
  typeInfer Γ (`fst e) | no ¬p = no (¬p ∘ Γ⊢fste∈A-inv ∘ proj₂)


  typeInfer Γ (`snd e)    with typeInfer Γ e
  ... | yes (A , Γ⊢e∈A) with whnf A | whnfReduct A
  ... | `sig S T | A↝*ΣST = yes (Substitution ⊨ T ⟨ `fst e /0⟩T , `snd (reduceInfer A↝*ΣST Γ⊢e∈A))
  ... | _              | _     = {!!}
  typeInfer Γ (`snd e) | no ¬p = no (¬p ∘ Γ⊢snde∈A-inv ∘ proj₂)


  typeInfer Γ (`ind p z s e) with typeInfer Γ e
  ... | yes q = {!!}
  ... | no ¬p = {!!}

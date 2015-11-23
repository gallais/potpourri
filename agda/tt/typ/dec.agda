module tt.typ.dec where

open import Data.Nat
open import Data.Fin hiding (_<_)
open import Data.Product as P
open import Data.Maybe
open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as PEq using (_≡_ ; subst)

open import tt.raw
open import tt.env
open import tt.sem
open import tt.typ

infix 1 _[_]*_
data _[_]*_ {A : Set} (a : A) (R : A → A → Set) : (b : A) → Set where
  done  : a [ R ]* a
  more  : {b c : A} → R a b → b [ R ]* c → a [ R ]* c

module typeCheck
       (_↝_        : {n : ℕ} (t u : Type n) → Set)
       (whnf       : {n : ℕ} → Type n → ∃ λ t → Type t ≡^Con t)
       (whnfReduct : {n : ℕ} (t : Type n) → t [ _↝_ ]* proj₁ (whnf t))
       (whnfSpec   : {n : ℕ} (t : Type n) →
                     (ex : ∃ λ s → (t [ _↝_ ]* s) × Type s ≡^Con s) →
                     Type proj₁ (whnf t) ≡^Con proj₁ ex)
       where

  open Typing _↝_

  -- Inversion lemmas

  Γ⊢A∋0-inv : {n : ℕ} {Γ : Context n} {A : Type n} → Γ ⊢ A ∋ `zro → A [ _↝_ ]* `nat
  Γ⊢A∋0-inv `zro         = done
  Γ⊢A∋0-inv (`red r typ) = more r $ Γ⊢A∋0-inv typ
  
  Γ⊢A∋Sm-inv : {n : ℕ} {Γ : Context n} {A : Type n} {m : Check n} → Γ ⊢ A ∋ `suc m → A [ _↝_ ]* `nat
  Γ⊢A∋Sm-inv (`suc _)     = done
  Γ⊢A∋Sm-inv (`red r typ) = more r $ Γ⊢A∋Sm-inv typ
  
  Γ⊢A∋Sm-inv′ : {n : ℕ} {Γ : Context n} {A : Type n} {m : Check n} → Γ ⊢ A ∋ `suc m → Γ ⊢ `nat ∋ m
  Γ⊢A∋Sm-inv′ (`suc m)     = m
  Γ⊢A∋Sm-inv′ (`red r typ) = Γ⊢A∋Sm-inv′ typ 
  
  Γ⊢A∋λb-inv : {n : ℕ} {Γ : Context n} {A : Type n} {b : Check (suc n)} →
               Γ ⊢ A ∋ `lam b → ∃ λ ST → A [ _↝_ ]* uncurry `pi ST
  Γ⊢A∋λb-inv (`lam _)     = , done
  Γ⊢A∋λb-inv (`red r typ) = P.map id (more r) $ Γ⊢A∋λb-inv typ
  
  Γ⊢A∋a,b-inv : {n : ℕ} {Γ : Context n} {A : Type n} {a b : Check n} →
                Γ ⊢ A ∋ `per a b → ∃ λ ST → A [ _↝_ ]* uncurry `sig ST
  Γ⊢A∋a,b-inv (`per _ _)   = , done
  Γ⊢A∋a,b-inv (`red r typ) = P.map id (more r) $ Γ⊢A∋a,b-inv typ
    
  Γ⊢fste∈A-inv : {n : ℕ} {Γ : Context n} {A : Type n} {e : Infer n} → Γ ⊢ `fst e ∈ A → ∃ λ B → Γ ⊢ e ∈ B
  Γ⊢fste∈A-inv (`fst typ)   = , typ
  Γ⊢fste∈A-inv (`red r typ) = Γ⊢fste∈A-inv typ

  Γ⊢snde∈A-inv : {n : ℕ} {Γ : Context n} {A : Type n} {e : Infer n} → Γ ⊢ `snd e ∈ A → ∃ λ B → Γ ⊢ e ∈ B
  Γ⊢snde∈A-inv (`snd typ)   = , typ
  Γ⊢snde∈A-inv (`red r typ) = Γ⊢snde∈A-inv typ

  Γ⊢anntA∈A-inv : {n : ℕ} {Γ : Context n} {A B : Type n} {t : Check n} → Γ ⊢ `ann t A ∈ B → Γ ⊢ A ∋ t
  Γ⊢anntA∈A-inv (`ann typ)   = typ
  Γ⊢anntA∈A-inv (`red r typ) = Γ⊢anntA∈A-inv typ

  Γ⊢appeu∈T-inv : {n : ℕ} {Γ : Context n} {A : Type n} {e : Infer n} {u : Check n} →
                  Γ ⊢ `app e u ∈ A → ∃ λ B → Γ ⊢ e ∈ B
  Γ⊢appeu∈T-inv (`app typ u) = , typ
  Γ⊢appeu∈T-inv (`red r typ) = Γ⊢appeu∈T-inv typ

  -- Coercions
  
  coerceInfer : {n : ℕ} {A B : Type n} (red : A [ _↝_ ]* B) {Γ : Context n} {e : Infer n} →
                Γ ⊢ e ∈ A → Γ ⊢ e ∈ B
  coerceInfer done         typ = typ
  coerceInfer (more r red) typ = coerceInfer red (`red r typ)

  coerceCheck : {n : ℕ} {A B : Type n} (red : B [ _↝_ ]* A) {Γ : Context n} {a : Check n} →
                Γ ⊢ A ∋ a → Γ ⊢ B ∋ a
  coerceCheck done         typ = typ
  coerceCheck (more r red) typ = `red r (coerceCheck red typ)



  typeInferVar : {n : ℕ} (Γ : Context n) (k : Fin n) → ∃ λ A → Γ ⊢var k ∈ A
  typeInferVar (_ ∙⟩ A) zero    = , zro
  typeInferVar (Γ ∙⟩ _) (suc k) = P.map (weakT extend) suc $ typeInferVar Γ k

  typeCheck : {n : ℕ} (Γ : Context n) (A : Type n) (a : Check n) → Dec (Γ ⊢ A ∋ a)
  typeInfer : {n : ℕ} (Γ : Context n) (e : Infer n) → Dec (∃ λ A → Γ ⊢ e ∈ A)
  
  typeCheck Γ A (`typ B) = {!!}


  typeCheck Γ A (`lam b) with whnf A | whnfReduct A | whnfSpec A
  ... | (`pi S T , _) | A↝*ΠST | _ with typeCheck (Γ ∙⟩ S) T b
  ... | yes p = yes (coerceCheck A↝*ΠST (`lam p))
  ... | no ¬p = no {!!}

  typeCheck Γ A (`lam b) | (`sig _ _ , _) | _ | spec = no (λ p → case spec (, proj₂ (Γ⊢A∋λb-inv p) , `pi) of λ ())
  typeCheck Γ A (`lam b) | (`nat     , _) | _ | spec = no (λ p → case spec (, proj₂ (Γ⊢A∋λb-inv p) , `pi) of λ ())
  typeCheck Γ A (`lam b) | (`set _   , _) | _ | spec = no (λ p → case spec (, proj₂ (Γ⊢A∋λb-inv p) , `pi) of λ ())
  typeCheck Γ A (`lam b) | (`elt _   , _) | _ | spec = no (λ p → case spec (, proj₂ (Γ⊢A∋λb-inv p) , `pi) of λ ())


  typeCheck Γ A (`per a b) with whnf A | whnfReduct A | whnfSpec A
  ... | (`sig S T , _) | A↝*ΣST | _ with typeCheck Γ S a | typeCheck Γ (Substitution ⊨ T ⟨ `ann a S /0⟩T) b
  ... | yes p₁ | yes p₂ = yes (coerceCheck A↝*ΣST (`per p₁ p₂))
  ... | no ¬p₁ | _      = no {!!}
  ... | yes p₁ | no ¬p₂ = no {!!}

  typeCheck Γ A (`per a b) | (`pi _ _ , _) | _ | sp = no (λ p → case sp (, proj₂ (Γ⊢A∋a,b-inv p) , `sig) of λ ())
  typeCheck Γ A (`per a b) | (`nat    , _) | _ | sp = no (λ p → case sp (, proj₂ (Γ⊢A∋a,b-inv p) , `sig) of λ ())
  typeCheck Γ A (`per a b) | (`set _  , _) | _ | sp = no (λ p → case sp (, proj₂ (Γ⊢A∋a,b-inv p) , `sig) of λ ())
  typeCheck Γ A (`per a b) | (`elt _  , _) | _ | sp = no (λ p → case sp (, proj₂ (Γ⊢A∋a,b-inv p) , `sig) of λ ())


  typeCheck Γ A `zro with whnf A | whnfReduct A | whnfSpec A
  ... | (`nat   , _)   | A↝*ℕ  | _ = yes (coerceCheck A↝*ℕ `zro)
  ... | (`sig _ _ , _) | A↝*ty | spec = no (λ p → case spec (`nat , Γ⊢A∋0-inv p , `nat) of (λ ()))
  ... | (`pi  _ _ , _) | A↝*ty | spec = no (λ p → case spec (`nat , Γ⊢A∋0-inv p , `nat) of (λ ()))
  ... | (`set _   , _) | A↝*ty | spec = no (λ p → case spec (`nat , Γ⊢A∋0-inv p , `nat) of (λ ()))
  ... | (`elt _   , _) | A↝*ty | spec = no (λ p → case spec (`nat , Γ⊢A∋0-inv p , `nat) of (λ ()))


  typeCheck Γ A (`suc a) with whnf A | whnfReduct A | whnfSpec A
  ... | (`nat   , _)   | A↝*ℕ  | _ with typeCheck Γ `nat a
  ... | yes p = yes (coerceCheck A↝*ℕ (`suc p))
  ... | no ¬p = no (¬p ∘ Γ⊢A∋Sm-inv′)
  typeCheck Γ A (`suc a) | (`sig _ _ , _) | A↝*ty | spec = no (λ p → case spec (, Γ⊢A∋Sm-inv p , `nat) of (λ ()))
  typeCheck Γ A (`suc a) | (`pi  _ _ , _) | A↝*ty | spec = no (λ p → case spec (, Γ⊢A∋Sm-inv p , `nat) of (λ ()))
  typeCheck Γ A (`suc a) | (`set _   , _) | A↝*ty | spec = no (λ p → case spec (, Γ⊢A∋Sm-inv p , `nat) of (λ ()))
  typeCheck Γ A (`suc a) | (`elt _   , _) | A↝*ty | spec = no (λ p → case spec (, Γ⊢A∋Sm-inv p , `nat) of (λ ()))



  typeCheck Γ A (`emb e) = {!!}

  -- Γ ⊢ `var k ∈ Γ ‼ k
  typeInfer Γ (`var k)   = yes $ P.map id `var $ typeInferVar Γ k

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
  ... | yes (A , Γ⊢e∈A) with whnf A | whnfReduct A
  ... | (`pi S T , _) | A↝*ΠST with typeCheck Γ S u
  ... | yes prf = yes (Substitution ⊨ T ⟨ `ann u S /0⟩T , `app (coerceInfer A↝*ΠST Γ⊢e∈A) prf)
  ... | no ầejgt = {!!}


  typeInfer Γ (`app e u) | yes (A , e∈A) | (whnfA , rA) | A↝B = {!!}


  typeInfer Γ (`fst e) with typeInfer Γ e
  ... | yes (A , Γ⊢e∈A) with whnf A | whnfReduct A
  ... | (`sig S T , _) | A↝*ΣST = yes (S , `fst (coerceInfer A↝*ΣST Γ⊢e∈A))
  ... | _              | _     = {!!}
  typeInfer Γ (`fst e) | no ¬p = no (¬p ∘ Γ⊢fste∈A-inv ∘ proj₂)


  typeInfer Γ (`snd e)    with typeInfer Γ e
  ... | yes (A , Γ⊢e∈A) with whnf A | whnfReduct A
  ... | (`sig S T , _) | A↝*ΣST = yes (Substitution ⊨ T ⟨ `fst e /0⟩T , `snd (coerceInfer A↝*ΣST Γ⊢e∈A))
  ... | _              | _     = {!!}
  typeInfer Γ (`snd e) | no ¬p = no (¬p ∘ Γ⊢snde∈A-inv ∘ proj₂)


  typeInfer Γ (`ind p z s e) with typeInfer Γ e
  ... | yes q = {!!}
  ... | no ¬p = {!!}

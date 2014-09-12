import lps.IMLL                  as IMLL
import lps.Linearity             as Linearity
import lps.Linearity.Action      as Action
import lps.Linearity.Consumption as Consumption
import lps.Search.BelongsTo      as BelongsTo

import lib.Context               as Con
open import lib.Maybe
open import lib.Nullary

open import Data.Empty
open import Data.Product hiding (map)
open import Data.Nat as ℕ
open import Function

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

module lps.Search.Calculus where

  module Calculus where

    open Con
    open Context
    open IMLL.Type
    open Linearity.Context
    open Action.Context
    module BTC = BelongsTo.Context

    infix 1 _⊢_⊣_
    data _⊢_⊣_ {γ : Con ty} (Γ : Usage γ) : (σ : ty) (Δ : Usage γ) → Set where
      `κ       : ∀ {Γ′ k} (pr : Γ BTC.∋ k ∈ Γ′) → Γ ⊢ `κ k ⊣ Γ′
      _`⊗ʳ_    : ∀ {σ τ Δ E} (s : Γ ⊢ σ ⊣ Δ) (t : Δ ⊢ τ ⊣ E) → Γ ⊢ σ `⊗ τ ⊣ E
      _`&ʳ_by_ : ∀ {σ τ Δ₁ Δ₂ E} (s : Γ ⊢ σ ⊣ Δ₁) (t : Γ ⊢ τ ⊣ Δ₂)
                   (pr : E ≡ Δ₁ ⊙ Δ₂) → Γ ⊢ σ `& τ ⊣ E

    open Context.Context

    _⊢?_ : ∀ {γ : Con ty} (Γ : Usage γ) (σ : ty) → Con (Σ[ Γ′ ∈ Usage γ ] Γ ⊢ σ ⊣ Γ′)
    Γ ⊢? `κ k   = map (uncurry $ λ Δ pr → Δ , `κ pr) $ k BTC.∈? Γ
    Γ ⊢? σ `⊗ τ = Γ ⊢? σ >>= uncurry $ λ Δ prσ →
                  Δ ⊢? τ >>= uncurry $ λ E prτ →
                  return $ E , prσ `⊗ʳ prτ
    Γ ⊢? σ `& τ = Γ ⊢? σ >>= uncurry $ λ Δ₁ prσ →
                  Γ ⊢? τ >>= uncurry $ λ Δ₂ prτ →
                  maybe (uncurry $ λ Δ pr → return $ Δ , prσ `&ʳ prτ by pr) ε (Δ₁ ⊙? Δ₂)

  module Examples where

    open Con
    open Context
    open IMLL.Type
    open IMLL
    open Linearity.Context
    open Calculus

    example⊗ :
      let A = `κ 0
          γ = ε ∙ A `⊗ A
      in Con (Σ[ Γ′ ∈ Usage γ ] inj[ γ ] ⊢ A `⊗ A ⊣ Γ′)
    example⊗ = _ ⊢? _ -- generates 2 proofs!

    example& :
      let A = `κ 0
          γ = ε ∙ (A `& (A `⊗ A))
      in Con (Σ[ Γ′ ∈ Usage γ ] inj[ γ ] ⊢ A ⊣ Γ′)
    example& = _ ⊢? _ -- generates 3 proofs only one of which is meaningful!

    example&′ :
      let A = `κ 0
          B = `κ 1
          φ = (A `& B) `& B
          γ = ε ∙ φ
      in Con (Σ[ Γ′ ∈ Usage γ ] inj[ γ ] ⊢ φ ⊣ Γ′)
    example&′ = _ ⊢? _ -- generates 4 proofs

    checks : length example⊗  ≡ 2
           × length example&  ≡ 3
           × length example&′ ≡ 4
    checks = Eq.refl , Eq.refl , Eq.refl

  module Soundness where

    module Type where

      open Con
      open Context
      open IMLL
      open IMLL.Type
      open Context.Context

      module Cover where

        open Linearity.Type
        open Linearity.Type.Cover
        open Consumption
        open Consumption.Type.Cover
        open Action.Type.Cover
        open Con.BelongsTo
        open BelongsTo.BelongsTo
        open IMLL.RewriteRules

        mutual

          ¬⊙diffˡ : {a : ty} {S S₁ S₂ A : Cover a} →
                  A ≡ S₁ ⊙ S → S ≡ S₁ ─ S₂ → ⊥
          ¬⊙diffˡ (sym prA) prS                = ¬⊙diffʳ prA prS
          ¬⊙diffˡ (`κ k) ()
          ¬⊙diffˡ (prA `⊗ prB) (prS `⊗ prT)    = ¬⊙diffˡ prA prS
          ¬⊙diffˡ (prA `⊗ prB) (prS `⊗ˡ _)     = ¬⊙diffˡ prA prS
          ¬⊙diffˡ (prA `⊗ prB) (_ `⊗ʳ prT)     = ¬⊙diffˡ prB prT
          ¬⊙diffˡ ([ prA ]`⊗ b) (prS `⊗[ .b ]) = ¬⊙diffˡ prA prS
          ¬⊙diffˡ (a `⊗[ prA ]) ([ .a ]`⊗ prS) = ¬⊙diffˡ prA prS
          ¬⊙diffˡ (a `& b) ()
          ¬⊙diffˡ ] prA [`&] prB [ ()
          ¬⊙diffˡ ] prB [`& ()
          ¬⊙diffˡ `&] prA [ ()
          ¬⊙diffˡ (prA `&[ b ]) (prS `&[ .b ]) = ¬⊙diffˡ prA prS
          ¬⊙diffˡ ([ a ]`& prA) ([ .a ]`& prS) = ¬⊙diffˡ prA prS

          ¬⊙diffʳ : {a : ty} {S S₁ S₂ A : Cover a} →
                  A ≡ S ⊙ S₁ → S ≡ S₁ ─ S₂ → ⊥
          ¬⊙diffʳ (sym prA) prS                = ¬⊙diffˡ prA prS
          ¬⊙diffʳ (`κ k) ()
          ¬⊙diffʳ (prA `⊗ prB) (prS `⊗ prT)    = ¬⊙diffʳ prA prS
          ¬⊙diffʳ (prA `⊗ prB) (prS `⊗ˡ _)     = ¬⊙diffʳ prA prS
          ¬⊙diffʳ (prA `⊗ prB) (_ `⊗ʳ prS)     = ¬⊙diffʳ prB prS
          ¬⊙diffʳ ([ prA ]`⊗ b) (prS `⊗[ .b ]) = ¬⊙diffʳ prA prS
          ¬⊙diffʳ (a `⊗[ prB ]) ([ .a ]`⊗ prT) = ¬⊙diffʳ prB prT
          ¬⊙diffʳ (a `& b) ()
          ¬⊙diffʳ ] prA [`&] prB [ ()
          ¬⊙diffʳ ] prB [`& ()
          ¬⊙diffʳ `&] prA [ ()
          ¬⊙diffʳ (prA `&[ b ]) (prS `&[ .b ]) = ¬⊙diffʳ prA prS
          ¬⊙diffʳ ([ a ]`& prB) ([ .a ]`& prT) = ¬⊙diffʳ prB prT

        ⟦A⊙A⟧ : {a : ty} {A A₁ : Cover a} (s : A ≡ A₁ ⊙ A₁) → A ≡ A₁
        ⟦A⊙A⟧ (sym s) = ⟦A⊙A⟧ s
        ⟦A⊙A⟧ (`κ k) = Eq.refl
        ⟦A⊙A⟧ (s₁ `⊗ s₂) rewrite ⟦A⊙A⟧ s₁ | ⟦A⊙A⟧ s₂ = Eq.refl
        ⟦A⊙A⟧ ([ s ]`⊗ b) rewrite ⟦A⊙A⟧ s = Eq.refl
        ⟦A⊙A⟧ (a `⊗[ s ]) rewrite ⟦A⊙A⟧ s = Eq.refl
        ⟦A⊙A⟧ (a `& b) = Eq.refl
        ⟦A⊙A⟧ (s `&[ b ]) rewrite ⟦A⊙A⟧ s = Eq.refl
        ⟦A⊙A⟧ ([ a ]`& s) rewrite ⟦A⊙A⟧ s = Eq.refl

        ⟦⊙⟧⊢ : (Γ₁ Γ₂ Δ : Con ty) {a σ τ : ty} →
          (E₁ : Cover a) (tm₁ : Γ₁ ++ ｢ E₁ ｣ ++ Δ ⊢ σ)
          (E₂ : Cover a) (tm₂ : Γ₂ ++ ｢ E₂ ｣ ++ Δ ⊢ τ) →
          (E : Cover a) → E ≡ E₁ ⊙ E₂ →
          Γ₁ ++ ｢ E ｣ ++ Δ ⊢ σ × Γ₂ ++ ｢ E ｣ ++ Δ ⊢ τ
        ⟦⊙⟧⊢ Γ₁ Γ₂ Δ E₁ tm₁ E₂ tm₂ _ (sym s) =
          let (tm₁ , tm₂) = ⟦⊙⟧⊢ Γ₂ Γ₁ Δ E₂ tm₂ E₁ tm₁ _ s
          in tm₂ , tm₁
        ⟦⊙⟧⊢ Γ₁ Γ₂ Δ .(`κ k) tm₁ .(`κ k) tm₂ ._ (`κ k) = tm₁ , tm₂
        ⟦⊙⟧⊢ Γ₁ Γ₂ Δ (S₁ `⊗ T₁) tm₁ (S₂ `⊗ T₂) tm₂ (S `⊗ T) (s₁ `⊗ s₂) =
          let (tm₁ , tm₂) = ⟦⊙⟧⊢ (Γ₁ ++ ｢ S₁ ｣) (Γ₂ ++ ｢ S₂ ｣) Δ
                   T₁ (tm-group⁻¹ Γ₁ ｢ S₁ ｣ ｢ T₁ ｣ Δ tm₁)
                   T₂ (tm-group⁻¹ Γ₂ ｢ S₂ ｣ ｢ T₂ ｣ Δ tm₂)
                   T s₂
              (tm₁ , tm₂) = ⟦⊙⟧⊢ Γ₁ Γ₂ (｢ T ｣ ++ Δ)
                   S₁ (tm-assoc (Γ₁ ++ ｢ S₁ ｣) ｢ T ｣ Δ tm₁)
                   S₂ (tm-assoc (Γ₂ ++ ｢ S₂ ｣) ｢ T ｣ Δ tm₂)
                   S s₁
          in (tm-group Γ₁ ｢ S ｣ ｢ T ｣ Δ $ tm-assoc⁻¹ (Γ₁ ++ ｢ S ｣) ｢ T ｣ Δ tm₁)
           , (tm-group Γ₂ ｢ S ｣ ｢ T ｣ Δ $ tm-assoc⁻¹ (Γ₂ ++ ｢ S ｣) ｢ T ｣ Δ tm₂)
        ⟦⊙⟧⊢ Γ₁ Γ₂ Δ ._ tm₁ ._ tm₂ ._ ([ s ]`⊗ b) = ⟦⊙⟧⊢ Γ₁ Γ₂ Δ _ tm₁ _ tm₂ _ s
        ⟦⊙⟧⊢ Γ₁ Γ₂ Δ ._ tm₁ ._ tm₂ ._ (a `⊗[ s ]) = ⟦⊙⟧⊢ Γ₁ Γ₂ Δ _ tm₁ _ tm₂ _ s
        ⟦⊙⟧⊢ Γ₁ Γ₂ Δ .(a `& b) tm₁ .(a `& b) tm₂ ._ (a `& b) = tm₁ , tm₂
        ⟦⊙⟧⊢ Γ₁ Γ₂ Δ ._ tm₁ ._ tm₂ ._ ] prA [`&] prB [ =
            ⟦isUsed⟧ Γ₁ Δ (prA `&[ _ ]) tm₁
          , ⟦isUsed⟧ Γ₂ Δ ([ _ ]`& prB) tm₂
        ⟦⊙⟧⊢ Γ₁ Γ₂ Δ ._ tm₁ ._ tm₂ ._ ] prB [`& = ⟦isUsed⟧ Γ₁ Δ ([ _ ]`& prB) tm₁ , tm₂
        ⟦⊙⟧⊢ Γ₁ Γ₂ Δ ._ tm₁ ._ tm₂ ._ `&] prA [ = ⟦isUsed⟧ Γ₁ Δ (prA `&[ _ ]) tm₁ , tm₂
        ⟦⊙⟧⊢ Γ₁ Γ₂ Δ ._ tm₁ ._ tm₂ ._ (s `&[ b ]) = ⟦⊙⟧⊢ Γ₁ Γ₂ Δ _ tm₁ _ tm₂ _ s
        ⟦⊙⟧⊢ Γ₁ Γ₂ Δ ._ tm₁ ._ tm₂ ._ ([ a ]`& s) = ⟦⊙⟧⊢ Γ₁ Γ₂ Δ _ tm₁ _ tm₂ _ s


        ⟦⊙⟧─ : {a : ty} {A B₁ B₂ : Cover a} →
            (E₁ : Cover a) (d₁ : B₁ ≡ A ─ E₁) (E₂ : Cover a) (d₂ : B₂ ≡ A ─ E₂) →
            {B : Cover a} → B ≡ B₁ ⊙ B₂ → Σ[ E ∈ Cover a ] B ≡ A ─ E × E ≡ E₁ ⊙ E₂
        ⟦⊙⟧─ E₁ d₁ E₂ d₂ (sym s) = let (E , d , s) = ⟦⊙⟧─ E₂ d₂ E₁ d₁ s in E , d , sym s
        ⟦⊙⟧─ ._ (d₁ `⊗ d₂) ._ (d₃ `⊗ d₄) (s₁ `⊗ s₂) =
          let (F₁ , d₁ , s₁) = ⟦⊙⟧─ _ d₁ _ d₃ s₁
              (F₂ , d₂ , s₂) = ⟦⊙⟧─ _ d₂ _ d₄ s₂
          in F₁ `⊗ F₂ , d₁ `⊗ d₂ , s₁ `⊗ s₂
        ⟦⊙⟧─ ._ (d₁ `⊗ˡ B₁) ._ (d₂ `⊗ˡ .B₁) (s₁ `⊗ s₂) =
          let (E , d , s) = ⟦⊙⟧─ _ d₁ _ d₂ s₁
          in E `⊗[ _ ]
           , Eq.subst (λ B → _ `⊗ B ≡ _ `⊗ _ ─ E `⊗[ _ ]) (Eq.sym $ ⟦A⊙A⟧ s₂) (d `⊗ˡ B₁)
           , [ s ]`⊗ _
        ⟦⊙⟧─ ._ (A₂ `⊗ʳ d₁) ._ (.A₂ `⊗ʳ d₂) (s₁ `⊗ s₂) =
          let (E , d , s) = ⟦⊙⟧─ _ d₁ _ d₂ s₂
          in [ _ ]`⊗ E
           , Eq.subst (λ B → B `⊗ _ ≡ _ `⊗ _ ─ [ _ ]`⊗ E) (Eq.sym $ ⟦A⊙A⟧ s₁) (A₂ `⊗ʳ d)
           , _ `⊗[ s ]
        ⟦⊙⟧─ ._ ([ A₁ ]`⊗ˡ B₁) ._ ([ A₂ ]`⊗ˡ .B₁) {A `⊗ B} (s₁ `⊗ s₂) =
             A `⊗[ _ ]
           , Eq.subst (λ B → _ `⊗ B ≡ [ _ ]`⊗ _ ─ A `⊗[ _ ])
                      (Eq.sym $ ⟦A⊙A⟧ s₂) ([ A ]`⊗ˡ B₁)
           , [ s₁ ]`⊗ _
        ⟦⊙⟧─ ._ ([ A₁ ]`⊗ˡʳ d₁) ._ ([ A₂ ]`⊗ˡʳ d₂) {A `⊗ B} (s₁ `⊗ s₂) =
           let (B , d , s) = ⟦⊙⟧─ _ d₁ _ d₂ s₂
           in A `⊗ B , [ A ]`⊗ˡʳ d , s₁ `⊗ s
        ⟦⊙⟧─ ._ (A₁ `⊗ʳ[ B₁ ]) ._ (.A₁ `⊗ʳ[ B₂ ]) {A `⊗ B} (s₁ `⊗ s₂) =
             [ _ ]`⊗ B 
           , Eq.subst (λ A → A `⊗ _ ≡ _ `⊗[ _ ] ─ [ _ ]`⊗ B)
                      (Eq.sym $ ⟦A⊙A⟧ s₁) (A₁ `⊗ʳ[ B ])
           , _ `⊗[ s₂ ]
        ⟦⊙⟧─ ._ (d₁ `⊗ˡʳ[ B₁ ]) ._ (d₂ `⊗ˡʳ[ B₂ ]) {A `⊗ B} (s₁ `⊗ s₂) =
           let (A , d , s) = ⟦⊙⟧─ _ d₁ _ d₂ s₁
           in A `⊗ B , d `⊗ˡʳ[ B ] , s `⊗ s₂
        ⟦⊙⟧─ ._ (d₁ `⊗[ b ]) ._ (d₂ `⊗[ .b ]) ([ s ]`⊗ .b) =
          let (E , d , s) = ⟦⊙⟧─ _ d₁ _ d₂ s
          in E `⊗[ b ] , d `⊗[ b ] , [ s ]`⊗ b
        ⟦⊙⟧─ ._ ([ σ ]`⊗ d₁) ._ ([ .σ ]`⊗ d₂) (.σ `⊗[ s ]) =
          let (E , d , s) = ⟦⊙⟧─ _ d₁ _ d₂ s
          in [ σ ]`⊗ E , [ σ ]`⊗ d , σ `⊗[ s ]
        ⟦⊙⟧─ E₁ () ._ ([ σ ]`& d₂) ] prA [`&] prB [
        ⟦⊙⟧─ E₁ d₁ E₂ () ] prB [`&
        ⟦⊙⟧─ E₁ d₁ E₂ () `&] prA [
        ⟦⊙⟧─ ._ (d₁ `&[ b ]) ._ (d₂ `&[ .b ]) (s `&[ .b ]) =
           let (E , d , s) = ⟦⊙⟧─ _ d₁ _ d₂ s
           in E `&[ b ] , d `&[ b ] , s `&[ b ]
        ⟦⊙⟧─ ._ ([ σ ]`& d₁) ._ ([ .σ ]`& d₂) ([ .σ ]`& s) =
           let (E , d , s) = ⟦⊙⟧─ _ d₁ _ d₂ s
           in [ σ ]`& E , [ σ ]`& d , [ σ ]`& s
        ⟦⊙⟧─ E₁ () E₂ d₂ (`κ k)
        ⟦⊙⟧─ E₁ () E₂ d₂ (a `& b)
        ⟦⊙⟧─ ._ (_  `⊗ d₂) ._ (_ `⊗ˡ _) (_ `⊗ s₂) = ⊥-elim $ ¬⊙diffʳ s₂ d₂
        ⟦⊙⟧─ ._ (d₁ `⊗ d₂) ._ (_ `⊗ʳ _) (s₁ `⊗ _) = ⊥-elim $ ¬⊙diffʳ s₁ d₁
        ⟦⊙⟧─ ._ (_ `⊗ˡ _) ._ (_ `⊗ d₃) (_ `⊗ s₂)  = ⊥-elim $ ¬⊙diffˡ s₂ d₃
        ⟦⊙⟧─ ._ (_ `⊗ˡ _) ._ (_ `⊗ʳ d₂) (_ `⊗ s₂) = ⊥-elim $ ¬⊙diffˡ s₂ d₂
        ⟦⊙⟧─ ._ (_ `⊗ʳ _) ._ (d₂ `⊗ _) (s₁ `⊗ _)  = ⊥-elim $ ¬⊙diffˡ s₁ d₂
        ⟦⊙⟧─ ._ (_ `⊗ʳ _) ._ (d₂ `⊗ˡ _) (s₁ `⊗ _) = ⊥-elim $ ¬⊙diffˡ s₁ d₂
        ⟦⊙⟧─ ._ ([ _ ]`⊗ˡ _) ._ ([ _ ]`⊗ˡʳ d₂) (_ `⊗ s₂) = ⊥-elim $ ¬⊙diffˡ s₂ d₂
        ⟦⊙⟧─ ._ (_ `⊗ʳ[ _ ]) ._ (d₂ `⊗ˡʳ[ _ ]) (s₁ `⊗ _) = ⊥-elim $ ¬⊙diffˡ s₁ d₂
        ⟦⊙⟧─ ._ ([ _ ]`⊗ˡʳ d₁) ._ ([ _ ]`⊗ˡ _) (_ `⊗ s₂) = ⊥-elim $ ¬⊙diffʳ s₂ d₁
        ⟦⊙⟧─ ._ (d₁ `⊗ˡʳ[ _ ]) ._ (_ `⊗ʳ[ _ ]) (s₁ `⊗ _) = ⊥-elim $ ¬⊙diffʳ s₁ d₁

        ⟦⊙⟧ : (Γ₁ Γ₂ Δ : Con ty) {a σ τ : ty} {A B₁ B₂ : Cover a} →
          (E₁ : Cover a) (d₁ : B₁ ≡ A ─ E₁) (tm₁ : Γ₁ ++ ｢ E₁ ｣ ++ Δ ⊢ σ)
          (E₂ : Cover a) (d₂ : B₂ ≡ A ─ E₂) (tm₂ : Γ₂ ++ ｢ E₂ ｣ ++ Δ ⊢ τ) →
          {B : Cover a} → B ≡ B₁ ⊙ B₂ →
          Σ[ E ∈ Cover a ] B ≡ A ─ E × Γ₁ ++ ｢ E ｣ ++ Δ ⊢ σ × Γ₂ ++ ｢ E ｣ ++ Δ ⊢ τ
        ⟦⊙⟧ Γ₁ Γ₂ Δ E₁ d₁ tm₁ E₂ d₂ tm₂ s =
          let (E , d , s) = ⟦⊙⟧─ E₁ d₁ E₂ d₂ s
              (tm₁ , tm₂) = ⟦⊙⟧⊢ Γ₁ Γ₂ Δ E₁ tm₁ E₂ tm₂ E s
          in E , d , tm₁ , tm₂

        open Interleaving

        ⟦>>=⟧ : {σ : ty} {S T U : Cover σ} (Γ₁ Δ₁ Γ₂ Δ₂ : Con ty) {a b : ty}
             (V₁ : Cover σ) (d₁ : T ≡ S ─ V₁) (tm₁ : Γ₁ ++ ｢ V₁ ｣ ++ Δ₁ ⊢ a)
             (V₂ : Cover σ) (d₂ : U ≡ T ─ V₂) (tm₂ : Γ₂ ++ ｢ V₂ ｣ ++ Δ₂ ⊢ b) →
             Σ[ V ∈ Cover σ ] Σ[ S₁ ∈ Con ty ] Σ[ S₂ ∈ Con ty ]
               U ≡ S ─ V × ｢ V ｣ ≡ S₁ ⋈ S₂
             × Γ₁ ++ S₁ ++ Δ₁ ⊢ a × Γ₂ ++ S₂ ++ Δ₂ ⊢ b
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ ._ ([ σ ]`& d₁) tm₁ ._ ([ .σ ]`& d₂) tm₂ =
          let (T , T₁ , T₂ , d , j , tms) = ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ _ d₁ tm₁ _ d₂ tm₂
          in [ σ ]`& T , T₁ , T₂ , [ σ ]`& d , j , tms
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ ._ (d₁ `&[ τ ]) tm₁ ._ (d₂ `&[ .τ ]) tm₂ =
          let (S , S₁ , S₂ , d , j , tms) = ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ _ d₁ tm₁ _ d₂ tm₂
          in S `&[ τ ] , S₁ , S₂ , d `&[ τ ] , j , tms
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ (S₁ `⊗ T₁) (d₁ `⊗ d₃) tm₁ (S₂ `⊗ T₂) (d₂ `⊗ d₄) tm₂ =
          let (T , T₁ , T₂ , dT , jT , tm₁ , tm₂) =
                ⟦>>=⟧ (Γ₁ ++ ｢ S₁ ｣) Δ₁ (Γ₂ ++ ｢ S₂ ｣) Δ₂ _ d₃
                (tm-group⁻¹ Γ₁ ｢ S₁ ｣ ｢ T₁ ｣ Δ₁ tm₁) _ d₄
                (tm-group⁻¹ Γ₂ ｢ S₂ ｣ ｢ T₂ ｣ Δ₂ tm₂)
              (S , S₁ , S₂ , dS , jS , tm₁ , tm₂) =
                ⟦>>=⟧ Γ₁ (T₁ ++ Δ₁) Γ₂ (T₂ ++ Δ₂) _ d₁
                (tm-assoc (Γ₁ ++ ｢ S₁ ｣) T₁ Δ₁ tm₁) _ d₂
                (tm-assoc (Γ₂ ++ ｢ S₂ ｣) T₂ Δ₂ tm₂)
          in S `⊗ T , S₁ ++ T₁ , S₂ ++ T₂ , dS `⊗ dT , jS Interleaving.++ jT ,
             tm-group Γ₁ S₁ T₁ Δ₁ (tm-assoc⁻¹ (Γ₁ ++ S₁) T₁ Δ₁ tm₁)
           , tm-group Γ₂ S₂ T₂ Δ₂ (tm-assoc⁻¹ (Γ₂ ++ S₂) T₂ Δ₂ tm₂)
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ (S₁ `⊗ T₁) (d₁ `⊗ d₂) tm₁ (S₂ `⊗[ τ ]) (d₃ `⊗ˡ T) tm₂ =
          let tm₁ = tm-assoc (Γ₁ ++ ｢ S₁ ｣) ｢ T₁ ｣ Δ₁ $
                      tm-group⁻¹ Γ₁ ｢ S₁ ｣ ｢ T₁ ｣ Δ₁ tm₁
              (S , S₁ , S₂ , d , j , tm₁ , tm₂) =
                ⟦>>=⟧ Γ₁ (｢ T₁ ｣ ++ Δ₁) Γ₂ Δ₂ S₁ d₁ tm₁ S₂ d₃ tm₂
          in S `⊗ T₁ , S₁ ++ ｢ T₁ ｣ , S₂ , d `⊗ d₂ , j Interleaving.++ˡ ｢ T₁ ｣
           , (tm-group Γ₁ S₁ ｢ T₁ ｣ Δ₁ $ tm-assoc⁻¹ (Γ₁ ++ S₁) ｢ T₁ ｣ Δ₁ tm₁) , tm₂ 
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ (S₁ `⊗ T₁) (d₁ `⊗ d₂) tm₁ ([ σ ]`⊗ T₂) (S `⊗ʳ d₃) tm₂ =
          let tm₁ = tm-group⁻¹ Γ₁ ｢ S₁ ｣ ｢ T₁ ｣ Δ₁ tm₁
              (T , T₁ , T₂ , d , j , tm₁ , tm₂) =
                ⟦>>=⟧ (Γ₁ ++ ｢ S₁ ｣) Δ₁ Γ₂ Δ₂ T₁ d₂ tm₁ T₂ d₃ tm₂
          in S₁ `⊗ T , ｢ S₁ ｣ ++ T₁ , T₂ , d₁ `⊗ d , ｢ S₁ ｣ Interleaving.ˡ++ j
           , tm-group Γ₁ ｢ S₁ ｣ T₁ Δ₁ tm₁ , tm₂
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ ._ ([ σ ]`⊗ d₁) tm₁ ._ ([ .σ ]`⊗ d₂) tm₂ = 
          let (T , T₁ , T₂ , d , j , tms) = ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ _ d₁ tm₁ _ d₂ tm₂
          in [ σ ]`⊗ T , T₁ , T₂ , [ σ ]`⊗ d , j , tms
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ ([ σ ]`⊗ T₁) ([ .σ ]`⊗ d₁) tm₁
                         (.S₂ `⊗[ τ ]) ([ S₂ ]`⊗ˡ T₂) tm₂ =
           S₂ `⊗ T₁ , ｢ T₁ ｣ , ｢ S₂ ｣ , [ S₂ ]`⊗ˡʳ d₁
         , ｢ S₂ ｣ Interleaving.ʳ++ˡ ｢ T₁ ｣ , tm₁ , tm₂
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ ([ .σ ]`⊗ T₁) ([ σ ]`⊗ d₁) tm₁
                         (.S₂ `⊗ T₂) ([ S₂ ]`⊗ˡʳ d₂) tm₂ =
          let (T , T₁ , T₂ , d , j , tm₁ , tm₂) =
                ⟦>>=⟧ Γ₁ Δ₁ (Γ₂ ++ ｢ S₂ ｣) Δ₂ T₁ d₁ tm₁ T₂ d₂ $
                tm-group⁻¹ Γ₂ ｢ S₂ ｣ ｢ T₂ ｣ Δ₂ tm₂
          in S₂ `⊗ T , T₁ , ｢ S₂ ｣ ++ T₂ , [ S₂ ]`⊗ˡʳ d
           , ｢ S₂ ｣ Interleaving.ʳ++ j , tm₁ , tm-group Γ₂ ｢ S₂ ｣ T₂ Δ₂ tm₂
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ ._ (d₁ `⊗[ τ ]) tm₁ ._ (d₂ `⊗[ .τ ]) tm₂ =
          let (S , S₁ , S₂ , d , j , tms) = ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ _ d₁ tm₁ _ d₂ tm₂
          in S `⊗[ τ ] , S₁ , S₂ , d `⊗[ τ ] , j , tms
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ (S₁ `⊗[ .τ ]) (d₁ `⊗[ τ ]) tm₁
                         ([ σ ]`⊗ .T₂) (S₂ `⊗ʳ[ T₂ ]) tm₂ =
            S₁ `⊗ T₂ , ｢ S₁ ｣ , ｢ T₂ ｣ , d₁ `⊗ˡʳ[ T₂ ]
          , ｢ S₁ ｣ Interleaving.ˡ++ʳ ｢ T₂ ｣ , tm₁ , tm₂
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ (S₁ `⊗[ .τ ]) (d₁ `⊗[ τ ]) tm₁
                         (S₂ `⊗ .T₂) (d₂ `⊗ˡʳ[ T₂ ]) tm₂ =
           let tm₂ = tm-assoc (Γ₂ ++ ｢ S₂ ｣) ｢ T₂ ｣ Δ₂ $
                     tm-group⁻¹ Γ₂ ｢ S₂ ｣ ｢ T₂ ｣ Δ₂ tm₂
               (S , S₁ , S₂ , d , j , tm₁ , tm₂) =
                 ⟦>>=⟧ Γ₁ Δ₁ Γ₂ (｢ T₂ ｣ ++ Δ₂) _ d₁ tm₁ _ d₂ tm₂
           in S `⊗ T₂ , S₁ , S₂ ++ ｢ T₂ ｣ , d `⊗ˡʳ[ T₂ ] ,
             j Interleaving.++ Interleaving.reflʳ {Γ = ｢ T₂ ｣} , tm₁
           , (tm-group Γ₂ S₂ ｢ T₂ ｣ Δ₂ $ tm-assoc⁻¹ (Γ₂ ++ S₂) ｢ T₂ ｣ Δ₂ tm₂)
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ (S₁ `⊗[ τ ]) (d₁ `⊗ˡ T) tm₁ (S₂ `⊗ T₂) (d₂ `⊗ d₃) tm₂ =
          let tm₂ = tm-assoc (Γ₂ ++ ｢ S₂ ｣) ｢ T₂ ｣ Δ₂ $
                    tm-group⁻¹ Γ₂ ｢ S₂ ｣ ｢ T₂ ｣ Δ₂ tm₂
              (S , S₁ , S₂ , d , j , tm₁ , tm₂) =
                ⟦>>=⟧ Γ₁ Δ₁ Γ₂ (｢ T₂ ｣ ++ Δ₂) S₁ d₁ tm₁ S₂ d₂ tm₂
          in S `⊗ T₂ , S₁ , S₂ ++ ｢ T₂ ｣ , d `⊗ d₃ , j Interleaving.++ʳ ｢ T₂ ｣
           , tm₁ , (tm-group Γ₂ S₂ ｢ T₂ ｣ Δ₂ $ tm-assoc⁻¹ (Γ₂ ++ S₂) ｢ T₂ ｣ Δ₂ tm₂)
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ ._ (d₁ `⊗ˡ T) tm₁ ._ (d₂ `⊗ˡ .T) tm₂ =
          let (S , S₁ , S₂ , d , jtms) = ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ _ d₁ tm₁ _ d₂ tm₂
          in S `⊗[ _ ] , S₁ , S₂ , d `⊗ˡ T , jtms
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ (S₁ `⊗[ τ ]) (d₁ `⊗ˡ T) tm₁ ([ σ ]`⊗ T₂) (S `⊗ʳ d₂) tm₂ =
            S₁ `⊗ T₂ , ｢ S₁ ｣ , ｢ T₂ ｣ , d₁ `⊗ d₂ , ｢ S₁ ｣ Interleaving.ˡ++ʳ ｢ T₂ ｣
          , tm₁ , tm₂
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ ([ σ ]`⊗ T₁) (S `⊗ʳ d₁) tm₁ (S₂ `⊗ T₂) (d₂ `⊗ d₃) tm₂ =
          let (T , T₁ , T₂ , d , j , tm₁ , tm₂) =
                ⟦>>=⟧ Γ₁ Δ₁ (Γ₂ ++ ｢ S₂ ｣) Δ₂ T₁ d₁ tm₁ T₂ d₃ $
                tm-group⁻¹ Γ₂ ｢ S₂ ｣ ｢ T₂ ｣ Δ₂ tm₂
          in S₂ `⊗ T , T₁ , ｢ S₂ ｣ ++ T₂ , d₂ `⊗ d , ｢ S₂ ｣ Interleaving.ʳ++ j
           , tm₁ , tm-group Γ₂ ｢ S₂ ｣ T₂ Δ₂ tm₂
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ ([ σ ]`⊗ T₁) (S `⊗ʳ d₁) tm₁ (S₂ `⊗[ τ ]) (d₂ `⊗ˡ T) tm₂ =
            S₂ `⊗ T₁ , ｢ T₁ ｣ , ｢ S₂ ｣ , d₂ `⊗ d₁ , ｢ S₂ ｣ Interleaving.ʳ++ˡ ｢ T₁ ｣
          , tm₁ , tm₂
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ ._ (S `⊗ʳ d₁) tm₁ ._ (.S `⊗ʳ d₂) tm₂ = 
          let (T , T₁ , T₂ , d , jtms) = ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ _ d₁ tm₁ _ d₂ tm₂
          in [ _ ]`⊗ T , T₁ , T₂ , S `⊗ʳ d , jtms
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ (.S₁ `⊗[ τ ]) ([ S₁ ]`⊗ˡ T) tm₁ (S₂ `⊗ T₂) (d₂ `⊗ d₃) tm₂ = {!!}
{-
          let (S , S₁ , S₂ , d , j , tm₁ , tm₂) =
                ⟦[]>>=⟧ Γ₁ Δ₁ Γ₂ (｢ T₂ ｣ ++ Δ₂) S₁ prσ tm₁ S₂ d₂ $
                  tm-assoc (Γ₂ ++ ｢ S₂ ｣) ｢ T₂ ｣ Δ₂ $
                  tm-group⁻¹ Γ₂ ｢ S₂ ｣ ｢ T₂ ｣ Δ₂ tm₂
          in S `⊗ T₂ , S₁ , S₂ ++ ｢ T₂ ｣ , [ d ]`⊗ˡʳ d₃ , j Interleaving.++ʳ ｢ T₂ ｣
           , tm₁ , (tm-group Γ₂ S₂ ｢ T₂ ｣ Δ₂ $ tm-assoc⁻¹ (Γ₂ ++ S₂) ｢ T₂ ｣ Δ₂ tm₂)
-}
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ (.S₁ `⊗[ τ ]) ([ S₁ ]`⊗ˡ T) tm₁ 
                         (S₂ `⊗[ .τ ]) (d₂ `⊗ˡ .T) tm₂ = {!!}
{-
          let (S , S₁ , S₂ , d , j , tms) = ⟦[]>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ S₁ prσ tm₁ S₂ d₂ tm₂
          in S `⊗[ τ ] , S₁ , S₂ , [ d ]`⊗ˡ T , j , tms-}
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ (.S₁ `⊗[ τ ]) ([ S₁ ]`⊗ˡ T₁) tm₁
                         ([ σ ]`⊗ T₂) (.S₁ `⊗ʳ d₂) tm₂ = {!!}
{-
            S₁ `⊗ T₂ , ｢ S₁ ｣ , ｢ T₂ ｣ , [ prσ ]`⊗ˡʳ d₂
          , ｢ S₁ ｣ Interleaving.ˡ++ʳ ｢ T₂ ｣ , tm₁ , tm₂
-}
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ (.S₁ `⊗ T₁) ([ S₁ ]`⊗ˡʳ d₁) tm₁ (S₂ `⊗ T₂) (d₂ `⊗ d₃) tm₂ = {!!}
{-
          let tm₁ = tm-group⁻¹ Γ₁ ｢ S₁ ｣ ｢ T₁ ｣ Δ₁ tm₁
              tm₂ = tm-group⁻¹ Γ₂ ｢ S₂ ｣ ｢ T₂ ｣ Δ₂ tm₂
              (T , T₁ , T₂ , dT , jT , tm₁ , tm₂) =
                ⟦>>=⟧ (Γ₁ ++ ｢ S₁ ｣) Δ₁ (Γ₂ ++ ｢ S₂ ｣) Δ₂ T₁ d₁ tm₁ T₂ d₃ tm₂ 
              tm₁ = tm-assoc (Γ₁ ++ ｢ S₁ ｣) T₁ Δ₁ tm₁
              tm₂ = tm-assoc (Γ₂ ++ ｢ S₂ ｣) T₂ Δ₂ tm₂
              (S , S₁ , S₂ , dS , jS , tm₁ , tm₂) =
                ⟦[]>>=⟧ Γ₁ (T₁ ++ Δ₁) Γ₂ (T₂ ++ Δ₂) S₁ prσ tm₁ S₂ d₂ tm₂
          in S `⊗ T , S₁ ++ T₁ , S₂ ++ T₂ , [ dS ]`⊗ˡʳ dT , jS Interleaving.++ jT
           , (tm-group Γ₁ S₁ T₁ Δ₁ $ tm-assoc⁻¹ (Γ₁ ++ S₁) T₁ Δ₁ tm₁)
           , (tm-group Γ₂ S₂ T₂ Δ₂ $ tm-assoc⁻¹ (Γ₂ ++ S₂) T₂ Δ₂ tm₂)
-}
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ (.S₁ `⊗ T₁) ([ S₁ ]`⊗ˡʳ d₁) tm₁
                         (S₂ `⊗[ τ ]) (d₂ `⊗ˡ T) tm₂ = {!!}
{-
          let tm₁ = tm-assoc (Γ₁ ++ ｢ S₁ ｣) ｢ T₁ ｣ Δ₁ $
                    tm-group⁻¹ Γ₁ ｢ S₁ ｣ ｢ T₁ ｣ Δ₁ tm₁
              (S , S₁ , S₂ , d , j , tm₁ , tm₂) =
                ⟦[]>>=⟧ Γ₁ (｢ T₁ ｣ ++ Δ₁) Γ₂ Δ₂ S₁ prσ tm₁ S₂ d₂ tm₂
          in S `⊗ T₁ , S₁ ++ ｢ T₁ ｣ , S₂ , [ d ]`⊗ˡʳ d₁ , j Interleaving.++ˡ ｢ T₁ ｣
           , (tm-group Γ₁ S₁ ｢ T₁ ｣ Δ₁ $ tm-assoc⁻¹ (Γ₁ ++ S₁) ｢ T₁ ｣ Δ₁ tm₁) , tm₂
-}
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ (.S₁ `⊗ T₁) ([ S₁ ]`⊗ˡʳ d₁) tm₁
                         ([ σ ]`⊗ T₂) (.S₁ `⊗ʳ d₂) tm₂ =
          let tm₁ = tm-group⁻¹ Γ₁ ｢ S₁ ｣ ｢ T₁ ｣ Δ₁ tm₁
              (T , T₁ , T₂ , d , j , tm₁ , tm₂) =
                ⟦>>=⟧ (Γ₁ ++ ｢ S₁ ｣) Δ₁ Γ₂ Δ₂ T₁ d₁ tm₁ T₂ d₂ tm₂
          in S₁ `⊗ T , ｢ S₁ ｣ ++ T₁ , T₂ , [ S₁ ]`⊗ˡʳ d
           , ｢ S₁ ｣ Interleaving.ˡ++ j , tm-group Γ₁ ｢ S₁ ｣ T₁ Δ₁ tm₁ , tm₂
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ ([ σ ]`⊗ .T₁) (S `⊗ʳ[ T₁ ]) tm₁ (S₂ `⊗ T₂) (d₂ `⊗ d₃) tm₂ = {!!}
{-
          let tm₂ = tm-group⁻¹ Γ₂ ｢ S₂ ｣ ｢ T₂ ｣ Δ₂ tm₂
              (T , T₁ , T₂ , d , j , tm₁ , tm₂) =
                ⟦[]>>=⟧ Γ₁ Δ₁ (Γ₂ ++ ｢ S₂ ｣) Δ₂ T₁ prτ tm₁ T₂ d₃ tm₂
          in S₂ `⊗ T , T₁ , ｢ S₂ ｣ ++ T₂ , d₂ `⊗ˡʳ[ d ] , ｢ S₂ ｣ Interleaving.ʳ++ j
           , tm₁ , tm-group Γ₂ ｢ S₂ ｣ T₂ Δ₂ tm₂
-}
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ ([ σ ]`⊗ .T₁) (S `⊗ʳ[ T₁ ]) tm₁
                         (S₂ `⊗[ τ ]) (d₂ `⊗ˡ .T₁) tm₂ =
            S₂ `⊗ T₁ , ｢ T₁ ｣ , ｢ S₂ ｣ , d₂ `⊗ˡʳ[ T₁ ]
          , ｢ S₂ ｣ Interleaving.ʳ++ˡ ｢ T₁ ｣ , tm₁ , tm₂
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ ([ σ ]`⊗ .T₁) (S `⊗ʳ[ T₁ ]) tm₁ ._ (.S `⊗ʳ d₂) tm₂ = {!!}
{-
          let (T , T₁ , T₂ , d , jtms) = ⟦[]>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ T₁ prτ tm₁ _ d₂ tm₂
          in [ σ ]`⊗ T , T₁ , T₂ , S `⊗ʳ[ d ] , jtms
-}
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ (S₁ `⊗ .T₁) (d₁ `⊗ˡʳ[ T₁ ]) tm₁ (S₂ `⊗ T₂) (d₂ `⊗ d₃) tm₂ = {!!}
{-
          let tm₁ = tm-group⁻¹ Γ₁ ｢ S₁ ｣ ｢ T₁ ｣ Δ₁ tm₁
              tm₂ = tm-group⁻¹ Γ₂ ｢ S₂ ｣ ｢ T₂ ｣ Δ₂ tm₂
              (T , T₁ , T₂ , dT , jT , tm₁ , tm₂) =
                ⟦[]>>=⟧ (Γ₁ ++ ｢ S₁ ｣) Δ₁ (Γ₂ ++ ｢ S₂ ｣) Δ₂ T₁ prτ tm₁ T₂ d₃ tm₂
              tm₁ = tm-assoc (Γ₁ ++ ｢ S₁ ｣) T₁ Δ₁ tm₁
              tm₂ = tm-assoc (Γ₂ ++ ｢ S₂ ｣) T₂ Δ₂ tm₂
              (S , S₁ , S₂ , dS , jS , tm₁ , tm₂) =
                ⟦>>=⟧ Γ₁ (T₁ ++ Δ₁) Γ₂ (T₂ ++ Δ₂) S₁ d₁ tm₁ S₂ d₂ tm₂
          in S `⊗ T , S₁ ++ T₁ , S₂ ++ T₂ , dS `⊗ˡʳ[ dT ] , jS Interleaving.++ jT
           , (tm-group Γ₁ S₁ T₁ Δ₁ $ tm-assoc⁻¹ (Γ₁ ++ S₁) T₁ Δ₁ tm₁)
           , (tm-group Γ₂ S₂ T₂ Δ₂ $ tm-assoc⁻¹ (Γ₂ ++ S₂) T₂ Δ₂ tm₂)
-}
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ (S₁ `⊗ .T₁) (d₁ `⊗ˡʳ[ T₁ ]) tm₁
                         (S₂ `⊗[ τ ]) (d₂ `⊗ˡ .T₁) tm₂ =
          let tm₁ = tm-assoc (Γ₁ ++ ｢ S₁ ｣) ｢ T₁ ｣ Δ₁ $
                    tm-group⁻¹ Γ₁ ｢ S₁ ｣ ｢ T₁ ｣ Δ₁ tm₁
              (S , S₁ , S₂ , d , j , tm₁ , tm₂) = 
                ⟦>>=⟧ Γ₁ (｢ T₁ ｣ ++ Δ₁) Γ₂ Δ₂ S₁ d₁ tm₁ S₂ d₂ tm₂
          in S `⊗ T₁ , S₁ ++ ｢ T₁ ｣ , S₂ , d `⊗ˡʳ[ T₁ ] , j Interleaving.++ˡ ｢ T₁ ｣
           , (tm-group Γ₁ S₁ ｢ T₁ ｣ Δ₁ $ tm-assoc⁻¹ (Γ₁ ++ S₁) ｢ T₁ ｣ Δ₁ tm₁) , tm₂
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ (S₁ `⊗ .T₁) (d₁ `⊗ˡʳ[ T₁ ]) tm₁
                         ([ σ ]`⊗ T₂) (S `⊗ʳ d₂) tm₂ = {!!}
{-
          let tm₁ = tm-group⁻¹ Γ₁ ｢ S₁ ｣ ｢ T₁ ｣ Δ₁ tm₁
              (T , T₁ , T₂ , d , j , tm₁ , tm₂) =
                ⟦[]>>=⟧ (Γ₁ ++ ｢ S₁ ｣) Δ₁ Γ₂ Δ₂ T₁ prτ tm₁ T₂ d₂ tm₂
          in S₁ `⊗ T , ｢ S₁ ｣ ++ T₁ , T₂ , d₁ `⊗ˡʳ[ d ] , ｢ S₁ ｣ Interleaving.ˡ++ j
           , tm-group Γ₁ ｢ S₁ ｣ T₁ Δ₁ tm₁ , tm₂
-}

{-
      module Usage where

        open Linearity.Type
        open Linearity.Type.Usage
        open Consumption.Type.Usage
        open Action.Type.Usage

        ⟦⊙⟧ : (Γ₁ Γ₂ Δ : Con ty) {a σ τ : ty} {A : Usage a} {B₁ B₂ : Usage a} →
              (E₁ : Usage a) (d₁ : B₁ ≡ A ─ E₁) (tm₁ : Γ₁ ++ ｢ E₁ ｣ ++ Δ ⊢ σ) 
              (E₂ : Usage a) (d₂ : B₂ ≡ A ─ E₂) (tm₂ : Γ₂ ++ ｢ E₂ ｣ ++ Δ ⊢ τ)
              {B : Usage a} → B ≡ B₁ ⊙ B₂ →
              Σ[ E ∈ Usage a ] B ≡ A ─ E ×
              Γ₁ ++ ｢ E ｣ ++ Δ ⊢ σ × Γ₂ ++ ｢ E ｣ ++ Δ ⊢ τ
        ⟦⊙⟧ Γ₁ Γ₂ Δ .([ a ]) `idˡ tm₁ .([ a ]) `idˡ tm₂ [ a ] = [ a ] , `idˡ , tm₁ , tm₂
        ⟦⊙⟧ Γ₁ Γ₂ Δ .([ a ]) `idˡ tm₁ .([ a ]) `idʳ tm₂ [ a ] = [ a ] , `idˡ , tm₁ , tm₂
        ⟦⊙⟧ Γ₁ Γ₂ Δ .([ a ]) `idʳ tm₁ .([ a ]) `idˡ tm₂ [ a ] = [ a ] , `idˡ , tm₁ , tm₂
        ⟦⊙⟧ Γ₁ Γ₂ Δ .([ a ]) `idʳ tm₁ .([ a ]) `idʳ tm₂ [ a ] = [ a ] , `idˡ , tm₁ , tm₂
        ⟦⊙⟧ Γ₁ Γ₂ Δ ._ `idˡ tm₁ ._ `idˡ tm₂ ] prA [ = [ _ ] , pr , tm₁ , tm₂
          where pr = Eq.subst (λ A → ] _ [ ≡ ] A [ ─ [ _ ]) (Cover.⟦A⊙A⟧ prA) `idˡ
        ⟦⊙⟧ Γ₁ Γ₂ Δ ._ `idʳ tm₁ ._ `idʳ tm₂ ] prA [ =
          ] _ [ , `idʳ , Cover.⟦⊙⟧⊢ Γ₁ Γ₂ Δ _ tm₁ _ tm₂ _ prA
        ⟦⊙⟧ Γ₁ Γ₂ Δ ._ ] prS₁ [ tm₁ ._ ] prS₂ [ tm₂ ] prA [ =
          let (S , prS , tms) = Cover.⟦⊙⟧ Γ₁ Γ₂ Δ _ prS₁ tm₁ _ prS₂ tm₂ prA
          in ] S [ , ] prS [ , tms
        ⟦⊙⟧ _ _ _ ._ `idˡ _ ._ ] prS [ _ ] prA [ = ⊥-elim $ Cover.¬⊙diffˡ prA prS
        ⟦⊙⟧ _ _ _ ._ ] prS [ _ ._ `idˡ _ ] prA [ = ⊥-elim $ Cover.¬⊙diffʳ prA prS

        open Interleaving

        ⟦>>=⟧ : {σ : ty} {S T U : Usage σ} (Γ₁ Δ₁ Γ₂ Δ₂ : Con ty) {a b : ty}
               (V₁ : Usage σ) (d₁ : T ≡ S ─ V₁) (tm₁ : Γ₁ ++ ｢ V₁ ｣ ++ Δ₁ ⊢ a)
               (V₂ : Usage σ) (d₂ : U ≡ T ─ V₂) (tm₂ : Γ₂ ++ ｢ V₂ ｣ ++ Δ₂ ⊢ b) →
               Σ[ V ∈ Usage σ ] Σ[ S₁ ∈ Con ty ] Σ[ S₂ ∈ Con ty ]
                 U ≡ S ─ V × ｢ V ｣ ≡ S₁ ⋈ S₂
               × Γ₁ ++ S₁ ++ Δ₁ ⊢ a × Γ₂ ++ S₂ ++ Δ₂ ⊢ b
        ⟦>>=⟧ = {!!}
{-
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ V₁ d₁ tm₁ ._ `idˡ tm₂ =
          V₁ , ｢ V₁ ｣ , ε , d₁ , reflˡ , tm₁ , tm₂
          where open Interleaving.Interleaving
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ ._ `idˡ tm₁ V₂ d₂ tm₂ =
          V₂ , ε , ｢ V₂ ｣ , d₂ , reflʳ , tm₁ , tm₂
          where open Interleaving.Interleaving
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ ._ ] prS₁ [ tm₁ ._ ] prS₂ [ tm₂ =
          let (S , S₁ , S₂ , d , jtms) =
                Cover.⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ _ prS₁ tm₁ _ prS₂ tm₂
          in ] S [ , S₁ , S₂ , ] d [ , jtms
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ ._ [ prS₁ ] tm₁ ._ ] prS₂ [ tm₂ = 
          let (S , S₁ , S₂ , d , jtms) =
                Cover.⟦[]>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ _ prS₁ tm₁ _ prS₂ tm₂
          in ] S [ , S₁ , S₂ , [ d ] , jtms
-}
    module Context where

      open Con
      open Context
      open IMLL.Type
      open IMLL
      open IMLL.RewriteRules
      open Pointwise
      open Context.Context
      open Consumption.Context
      open Action.Context
      open Linearity
      open Linearity.Context

      ⟦⊙⟧ : {γ : Con ty} (δ : Con ty) (Γ : Usage γ) {σ τ : ty} (Δ₁ Δ₂ : Usage γ)
          (E₁ : Usage γ) (d₁ : Δ₁ ≡ Γ ─ E₁) (tm₁ : ｢ E₁ ｣ ++ δ ⊢ σ)
          (E₂ : Usage γ) (d₂ : Δ₂ ≡ Γ ─ E₂) (tm₂ : ｢ E₂ ｣ ++ δ ⊢ τ)
          {Δ : Usage γ} → Δ  ≡ Δ₁ ⊙ Δ₂ →
          Σ[ E ∈ Usage γ ] Δ  ≡ Γ ─ E × ｢ E ｣ ++ δ ⊢ σ × ｢ E ｣ ++ δ ⊢ τ
      ⟦⊙⟧ δ ε ε ε ε d₁ tm₁ ε d₂ tm₂ ε = ε , ε , tm₁ , tm₂
      ⟦⊙⟧ {γ ∙ a} δ (Γ ∙ S) (Δ₁ ∙ D₁) (Δ₂ ∙ D₂)
        (E₁ ∙ e₁) (d₁ ∙ t₁) tm₁ (E₂ ∙ e₂) (d₂ ∙ t₂) tm₂ (sync ∙ prS) =
        let (f , df , tmσ , tmτ) =
              Type.Usage.⟦⊙⟧ ｢ E₁ ｣ ｢ E₂ ｣ δ e₁ t₁ tm₁ e₂ t₂ tm₂ prS
            (E , dE , tmσ , tmτ)  =
              ⟦⊙⟧ (LTU.｢ f ｣ ++ δ) Γ Δ₁ Δ₂
                E₁ d₁ (tm-assoc ｢ E₁ ｣ LTU.｢ f ｣ δ tmσ)
                E₂ d₂ (tm-assoc ｢ E₂ ｣ LTU.｢ f ｣ δ tmτ) sync
        in E ∙ f , dE ∙ df , tm-assoc⁻¹ ｢ E ｣ LTU.｢ f ｣ δ tmσ
                           , tm-assoc⁻¹ ｢ E ｣ LTU.｢ f ｣ δ tmτ

      ⟦&ʳ⟧ : {γ : Con ty} {Γ : Usage γ} {σ τ : ty} {Δ₁ Δ₂ : Usage γ} →
            Σ[ E ∈ Usage γ ] Δ₁ ≡ Γ ─ E × ｢ E ｣ ⊢ σ → 
            Σ[ E ∈ Usage γ ] Δ₂ ≡ Γ ─ E × ｢ E ｣ ⊢ τ →
            (Δ : Usage γ) → Δ  ≡ Δ₁ ⊙ Δ₂ →
            Σ[ E ∈ Usage γ ] Δ  ≡ Γ ─ E × ｢ E ｣ ⊢ σ × ｢ E ｣ ⊢ τ
      ⟦&ʳ⟧ (E₁ , d₁ , tm₁) (E₂ , d₂ , tm₂) Δ = ⟦⊙⟧ ε _ _ _ E₁ d₁ tm₁ E₂ d₂ tm₂

      open Interleaving
      open Interleaving.RewriteRules

      ⟦>>=⟧ : (γ : Con ty) {Γ Δ E : Usage γ} (C A B : Con ty)
             {σ τ : ty} (pr : C ≡ A ⋈ B)
             (F₁ : Usage γ) (d₁ : Δ ≡ Γ ─ F₁) (tm₁ : ｢ F₁ ｣ ++ A ⊢ σ)
             (F₂ : Usage γ) (d₂ : E ≡ Δ ─ F₂) (tm₂ : ｢ F₂ ｣ ++ B ⊢ τ) →
             Σ[ F ∈ Usage γ ] Σ[ E₁ ∈ Con ty ] Σ[ E₂ ∈ Con ty ]
               E ≡ Γ ─ F × ｢ F ｣ ++ C ≡ E₁ ++ A ⋈ E₂ ++ B
             × E₁ ++ A ⊢ σ × E₂ ++ B ⊢ τ
      ⟦>>=⟧ ε C A B pr ε ε h₁ ε ε h₂ = ε , ε , ε , ε , ε Interleaving.++ pr , h₁ , h₂
      ⟦>>=⟧ (γ ∙ σ) C A B pr (F₁ ∙ V₁) (D₁ ∙ d₁) tm₁ (F₂ ∙ V₂) (D₂ ∙ d₂) tm₂ =
        let (V , V₁ , V₂ , d , j , tm₁ , tm₂) =
              Type.Usage.⟦>>=⟧ ｢ F₁ ｣ A ｢ F₂ ｣ B V₁ d₁ tm₁ V₂ d₂ tm₂
            (F , F₁ , F₂ , D , J , tm₁ , tm₂) =
              ⟦>>=⟧ γ (LTU.｢ V ｣ ++ C) (V₁ ++ A) (V₂ ++ B) (j Interleaving.++ pr)
                   F₁ D₁ (tm-assoc ｢ F₁ ｣ V₁ A tm₁)
                   F₂ D₂ (tm-assoc ｢ F₂ ｣ V₂ B tm₂)
        in F ∙ V , F₁ ++ V₁ , F₂ ++ V₂ , D ∙ d
         , ⋈-assoc⁻¹ ｢ F ｣ C F₁ A F₂ B J
         , tm-assoc⁻¹ F₁ V₁ A tm₁
         , tm-assoc⁻¹ F₂ V₂ B tm₂

      ⟦⊗ʳ⟧ : {γ : Con ty} {Γ Δ E : Usage γ} {σ τ : ty} →
            Σ[ F ∈ Usage γ ] Δ ≡ Γ ─ F × ｢ F ｣ ⊢ σ → 
            Σ[ F ∈ Usage γ ] E ≡ Δ ─ F × ｢ F ｣ ⊢ τ →
            Σ[ F ∈ Usage γ ] Σ[ E₁ ∈ Con ty ] Σ[ E₂ ∈ Con ty ]
               E ≡ Γ ─ F × ｢ F ｣ ≡ E₁ ⋈ E₂ × E₁ ⊢ σ × E₂ ⊢ τ
      ⟦⊗ʳ⟧ (F₁ , d₁ , tm₁) (F₂ , d₂ , tm₂) = ⟦>>=⟧ _ ε ε ε ε F₁ d₁ tm₁ F₂ d₂ tm₂

      open Calculus

      ⟦_⟧ : {γ : Con ty} {Γ : Usage γ} {σ : ty} {Δ : Usage γ} (pr : Γ ⊢ σ ⊣ Δ) →
            Σ[ E ∈ Usage γ ] Δ ≡ Γ ─ E × ｢ E ｣ ⊢ σ
      ⟦ `κ pr              ⟧ = BTC.Soundness.⟦ pr ⟧
      ⟦ prσ `⊗ʳ prτ        ⟧ =
        let (F , E₁ , E₂ , diff , inter , tmσ , tmτ) = ⟦⊗ʳ⟧ ⟦ prσ ⟧ ⟦ prτ ⟧
        in F , diff , tmσ `⊗ʳ tmτ by inter
      ⟦ prσ `&ʳ prτ by acc ⟧ =
        let (E , diff , tmσ , tmτ) = ⟦&ʳ⟧ ⟦ prσ ⟧ ⟦ prτ ⟧ _ acc
        in E , diff , tmσ `&ʳ tmτ
-}
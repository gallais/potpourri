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

    ⊢∈ : ∀ {γ} {Γ : Usage γ} {k : ℕ} →
         Σ[ Γ′ ∈ Usage γ ] Γ BTC.∋ k ∈ Γ′ →
         Σ[ Γ′ ∈ Usage γ ] Γ ⊢ `κ k ⊣ Γ′
    ⊢∈ (Γ′ , pr) = Γ′ , `κ pr

    _⊢?_ : ∀ {γ : Con ty} (Γ : Usage γ) (σ : ty) → Con (Σ[ Γ′ ∈ Usage γ ] Γ ⊢ σ ⊣ Γ′)
    Γ ⊢? `κ k   = map ⊢∈ $ k BTC.∈? Γ
    Γ ⊢? σ `⊗ τ = Γ ⊢? σ >>= uncurry $ λ Δ prσ →
                  Δ ⊢? τ >>= uncurry $ λ E prτ →
                  return $ E , prσ `⊗ʳ prτ
    Γ ⊢? σ `& τ = Γ ⊢? σ >>= uncurry $ λ Δ₁ prσ →
                  Γ ⊢? τ >>= uncurry $ λ Δ₂ prτ →
                  case Δ₁ ⊙? Δ₂ of λ
                     { none            → ε
                     ; (some (Δ , pr)) → return $ Δ , prσ `&ʳ prτ by pr }

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


        bim : {σ : ty} {S S₂ : Cover σ} (prS : isUsed S₂) →
              S₂ ≡[ σ ]─ S → isUsed S
        bim (`κ k)       (`κ .k) = `κ k
        bim (prA `⊗ prB) (pra `⊗ prb) = bim prA pra `⊗ bim prB prb
        bim (a `& b) (.a `& .b) = a `& b
        bim (prA `&[ b ]) (prS `&[ .b ]) = bim prA prS `&[ b ]
        bim ([ a ]`& prB) ([ .a ]`& prT) = [ a ]`& bim prB prT


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

        mutual

          ⟦⊙⟧ : (Γ₁ Γ₂ Δ : Con ty) {a σ τ : ty} {A B₁ B₂ : Cover a} →
            (E₁ : Cover a) (d₁ : B₁ ≡ A ─ E₁) (tm₁ : Γ₁ ++ ｢ E₁ ｣ ++ Δ ⊢ σ)
            (E₂ : Cover a) (d₂ : B₂ ≡ A ─ E₂) (tm₂ : Γ₂ ++ ｢ E₂ ｣ ++ Δ ⊢ τ) →
            {B : Cover a} → B ≡ B₁ ⊙ B₂ →
            Σ[ E ∈ Cover a ] B ≡ A ─ E × Γ₁ ++ ｢ E ｣ ++ Δ ⊢ σ × Γ₂ ++ ｢ E ｣ ++ Δ ⊢ τ
          ⟦⊙⟧ Γ₁ Γ₂ Δ E₁ d₁ tm₁ E₂ d₂ tm₂ (sym s) =
            let (E , d , tm₂ , tm₁) = ⟦⊙⟧ Γ₂ Γ₁ Δ E₂ d₂ tm₂ E₁ d₁ tm₁ s
            in E , d , tm₁ , tm₂
          ⟦⊙⟧ Γ₁ Γ₂ Δ (S₁ `⊗ T₁) (d₁ `⊗ d₃) tm₁ 
                     (S₂ `⊗ T₂) (d₂ `⊗ d₄) tm₂ (s₁ `⊗ s₂) =
              let tm₁ = tm-group⁻¹ Γ₁ ｢ S₁ ｣ ｢ T₁ ｣ Δ tm₁
                  tm₂ = tm-group⁻¹ Γ₂ ｢ S₂ ｣ ｢ T₂ ｣ Δ tm₂
                  (T , dT , tm₁ , tm₂) = ⟦⊙⟧ (Γ₁ ++ ｢ S₁ ｣) (Γ₂ ++ ｢ S₂ ｣) Δ
                                         T₁ d₃ tm₁ T₂ d₄ tm₂ s₂
                  tm₁ = tm-assoc (Γ₁ ++ ｢ S₁ ｣) ｢ T ｣ Δ tm₁
                  tm₂ = tm-assoc (Γ₂ ++ ｢ S₂ ｣) ｢ T ｣ Δ tm₂
                  (S , dS , tm₁ , tm₂) =
                    ⟦⊙⟧ Γ₁ Γ₂ (｢ T ｣ ++ Δ) S₁ d₁ tm₁ S₂ d₂ tm₂ s₁
              in S `⊗ T , dS `⊗ dT
               , (tm-group Γ₁ ｢ S ｣ ｢ T ｣ Δ $ tm-assoc⁻¹ (Γ₁ ++ ｢ S ｣) ｢ T ｣ Δ tm₁)
               , (tm-group Γ₂ ｢ S ｣ ｢ T ｣ Δ $ tm-assoc⁻¹ (Γ₂ ++ ｢ S ｣) ｢ T ｣ Δ tm₂)
          ⟦⊙⟧ Γ₁ Γ₂ Δ ._ (d₁ `⊗ˡ _) tm₁ ._ (d₂ `⊗ˡ ._) tm₂ (s₁ `⊗ s₂) =
            let (S , d , tms) = ⟦⊙⟧ Γ₁ Γ₂ Δ _ d₁ tm₁ _ d₂ tm₂ s₁
            in S `⊗[ _ ] , Eq.subst (λ B → _ `⊗ _ ≡ _ `⊗ B ─ _) (⟦A⊙A⟧ s₂) (d `⊗ˡ _) 
             , tms
          ⟦⊙⟧ Γ₁ Γ₂ Δ ._ (_ `⊗ʳ d₁) tm₁ ._ (._ `⊗ʳ d₂) tm₂ (s₁ `⊗ s₂) =
            let (T , d , tms) = ⟦⊙⟧ Γ₁ Γ₂ Δ _ d₁ tm₁ _ d₂ tm₂ s₂
            in [ _ ]`⊗ T , Eq.subst (λ A → _ `⊗ _ ≡ A `⊗ _ ─ _) (⟦A⊙A⟧ s₁) (_ `⊗ʳ d)
             , tms
          ⟦⊙⟧ Γ₁ Γ₂ Δ ._ ([ prσ₁ ]`⊗ˡ B₂) tm₁ ._ ([ prσ₂ ]`⊗ˡ .B₂) tm₂ (s₁ `⊗ s₂) =
            let (S , d , tms) = ⟦[⊙]⟧ Γ₁ Γ₂ Δ _ prσ₁ tm₁ _ prσ₂ tm₂ s₁
            in S `⊗[ _ ]
            , Eq.subst (λ B → _ `⊗ _ ≡ [ _ ]`⊗ B ─ _) (⟦A⊙A⟧ s₂) ([ d ]`⊗ˡ _)
            , tms
          ⟦⊙⟧ Γ₁ Γ₂ Δ (S₁ `⊗ T₁) ([ prσ₁ ]`⊗ˡʳ d₁) tm₁
                     (S₂ `⊗ T₂) ([ prσ₂ ]`⊗ˡʳ d₂) tm₂ (s₁ `⊗ s₂) =
            let tm₁ = tm-group⁻¹ Γ₁ ｢ S₁ ｣ ｢ T₁ ｣ Δ tm₁
                tm₂ = tm-group⁻¹ Γ₂ ｢ S₂ ｣ ｢ T₂ ｣ Δ tm₂
                (T , dT , tm₁ , tm₂) =
                  ⟦⊙⟧ (Γ₁ ++ ｢ S₁ ｣) (Γ₂ ++ ｢ S₂ ｣) Δ T₁ d₁ tm₁ T₂ d₂ tm₂ s₂
                tm₁ = tm-assoc (Γ₁ ++ ｢ S₁ ｣) ｢ T ｣ Δ tm₁
                tm₂ = tm-assoc (Γ₂ ++ ｢ S₂ ｣) ｢ T ｣ Δ tm₂
                (S , dS , tm₁ , tm₂) =
                  ⟦[⊙]⟧ Γ₁ Γ₂ (｢ T ｣ ++ Δ) S₁ prσ₁ tm₁ S₂ prσ₂ tm₂ s₁
            in S `⊗ T , [ dS ]`⊗ˡʳ dT
             , (tm-group Γ₁ ｢ S ｣ ｢ T ｣ Δ $ tm-assoc⁻¹ (Γ₁ ++ ｢ S ｣) ｢ T ｣ Δ tm₁)
             , (tm-group Γ₂ ｢ S ｣ ｢ T ｣ Δ $ tm-assoc⁻¹ (Γ₂ ++ ｢ S ｣) ｢ T ｣ Δ tm₂)
          ⟦⊙⟧ Γ₁ Γ₂ Δ ._ (_ `⊗ʳ[ prτ₁ ]) tm₁ ._ (._ `⊗ʳ[ prτ₂ ]) tm₂ (s₁ `⊗ s₂) =
            let (T , d , tms) = ⟦[⊙]⟧ Γ₁ Γ₂ Δ _ prτ₁ tm₁ _ prτ₂ tm₂ s₂
            in [ _ ]`⊗ T
            , Eq.subst (λ B → _ `⊗ _ ≡ B `⊗[ _ ] ─ _) (⟦A⊙A⟧ s₁) ( _ `⊗ʳ[ d ])
            , tms
          ⟦⊙⟧ Γ₁ Γ₂ Δ (S₁ `⊗ T₁) (d₁ `⊗ˡʳ[ prτ₁ ]) tm₁
                     (S₂ `⊗ T₂) (d₂ `⊗ˡʳ[ prτ₂ ]) tm₂ (s₁ `⊗ s₂) =
            let tm₁ = tm-group⁻¹ Γ₁ ｢ S₁ ｣ ｢ T₁ ｣ Δ tm₁
                tm₂ = tm-group⁻¹ Γ₂ ｢ S₂ ｣ ｢ T₂ ｣ Δ tm₂
                (T , dT , tm₁ , tm₂) =
                  ⟦[⊙]⟧ (Γ₁ ++ ｢ S₁ ｣) (Γ₂ ++ ｢ S₂ ｣) Δ T₁ prτ₁ tm₁ T₂ prτ₂ tm₂ s₂
                tm₁ = tm-assoc (Γ₁ ++ ｢ S₁ ｣) ｢ T ｣ Δ tm₁
                tm₂ = tm-assoc (Γ₂ ++ ｢ S₂ ｣) ｢ T ｣ Δ tm₂
                (S , dS , tm₁ , tm₂) =
                  ⟦⊙⟧ Γ₁ Γ₂ (｢ T ｣ ++ Δ) S₁ d₁ tm₁ S₂ d₂ tm₂ s₁
            in S `⊗ T , dS `⊗ˡʳ[ dT ]
             , (tm-group Γ₁ ｢ S ｣ ｢ T ｣ Δ $ tm-assoc⁻¹ (Γ₁ ++ ｢ S ｣) ｢ T ｣ Δ tm₁)
             , (tm-group Γ₂ ｢ S ｣ ｢ T ｣ Δ $ tm-assoc⁻¹ (Γ₂ ++ ｢ S ｣) ｢ T ｣ Δ tm₂)
          ⟦⊙⟧ Γ₁ Γ₂ Δ ._ (d₁ `⊗[ _ ]) tm₁ ._ (d₂ `⊗[ ._ ]) tm₂ ([ sync ]`⊗ ._) =
            let (E , d , tms) = ⟦⊙⟧ Γ₁ Γ₂ Δ _ d₁ tm₁ _ d₂ tm₂ sync
            in E `⊗[ _ ] , d `⊗[ _ ] , tms
          ⟦⊙⟧ Γ₁ Γ₂ Δ ._ ([ _ ]`⊗ d₁) tm₁ ._ ([ ._ ]`⊗ d₂) tm₂ (._ `⊗[ sync ]) =
            let (E , d , tms) = ⟦⊙⟧ Γ₁ Γ₂ Δ _ d₁ tm₁ _ d₂ tm₂ sync
            in [ _ ]`⊗ E , [ _ ]`⊗ d , tms
          ⟦⊙⟧ Γ₁ Γ₂ Δ ._ (d₁ `&[ b ]) tm₁ ._ (d₂ `&[ .b ]) tm₂ (sync `&[ .b ]) =
             let (E , d , tms) = ⟦⊙⟧ Γ₁ Γ₂ Δ _ d₁ tm₁ _ d₂ tm₂ sync
             in E `&[ _ ] , d `&[ _ ] , tms
          ⟦⊙⟧ Γ₁ Γ₂ Δ ._ ([ a ]`& d₁) tm₁ ._ ([ .a ]`& d₂) tm₂ ([ .a ]`& sync) =
             let (E , d , tms) = ⟦⊙⟧ Γ₁ Γ₂ Δ _ d₁ tm₁ _ d₂ tm₂ sync
             in [ _ ]`& E , [ _ ]`& d , tms
          ⟦⊙⟧ Γ₁ Γ₂ Δ E₁ () tm₁ E₂ d₂ tm₂ (`κ k)
          ⟦⊙⟧ Γ₁ Γ₂ Δ E₁ () tm₁ E₂ d₂ tm₂ (a `& b)
          ⟦⊙⟧ Γ₁ Γ₂ Δ E₁ () tm₁ ._ ([ a ]`& d₂) tm₂ ] prA [`&] prB [
          ⟦⊙⟧ Γ₁ Γ₂ Δ ._ ([ a ]`& d₁) tm₁ E₂ () tm₂ ] prB [`&
          ⟦⊙⟧ Γ₁ Γ₂ Δ ._ (d₁ `&[ b ]) tm₁ E₂ () tm₂ `&] prA [
          ⟦⊙⟧ Γ₁ Γ₂ Δ ._ (_ `⊗ d₂) _ ._ (_ `⊗ˡ _) _ (_ `⊗ s₂) =
             ⊥-elim $ ¬⊙diffʳ s₂ d₂
          ⟦⊙⟧ Γ₁ Γ₂ Δ ._ (d₁ `⊗ _) _ ._ (_ `⊗ʳ _) _ (s₁ `⊗ _) =
             ⊥-elim $ ¬⊙diffʳ s₁ d₁
          ⟦⊙⟧ Γ₁ Γ₂ Δ ._ (_ `⊗ˡ _) _ ._ (_ `⊗ d₃) _ (_ `⊗ s₂) =
             ⊥-elim $ ¬⊙diffˡ s₂ d₃
          ⟦⊙⟧ Γ₁ Γ₂ Δ ._ (_ `⊗ˡ _) _ ._ (_ `⊗ʳ d₂) _ (_ `⊗ s₂) =
            ⊥-elim $ ¬⊙diffˡ s₂ d₂
          ⟦⊙⟧ Γ₁ Γ₂ Δ ._ (_ `⊗ʳ _) _ ._ (d₂ `⊗ _) _ (s₁ `⊗ _) =
            ⊥-elim $ ¬⊙diffˡ s₁ d₂
          ⟦⊙⟧ Γ₁ Γ₂ Δ ._ (_ `⊗ʳ _) _ ._ (d₂ `⊗ˡ _) _ (s₁ `⊗ _) =
            ⊥-elim $ ¬⊙diffˡ s₁ d₂
          ⟦⊙⟧ Γ₁ Γ₂ Δ ._ ([ _ ]`⊗ˡ _) _ ._ ([ _ ]`⊗ˡʳ d₂) _ (_ `⊗ s₂) =
            ⊥-elim $ ¬⊙diffˡ s₂ d₂
          ⟦⊙⟧ Γ₁ Γ₂ Δ ._ ([ _ ]`⊗ˡʳ d₁) _ ._ ([ _ ]`⊗ˡ _) _ (_ `⊗ s₂) =
            ⊥-elim $ ¬⊙diffʳ s₂ d₁
          ⟦⊙⟧ Γ₁ Γ₂ Δ ._ (_ `⊗ʳ[ _ ]) _ ._ (d₂ `⊗ˡʳ[ _ ]) tm₂ (s₁ `⊗ _) =
            ⊥-elim $ ¬⊙diffˡ s₁ d₂
          ⟦⊙⟧ Γ₁ Γ₂ Δ ._ (d₁ `⊗ˡʳ[ _ ]) _ ._ (_ `⊗ʳ[ _ ]) _ (s₁ `⊗ _) =
            ⊥-elim $ ¬⊙diffʳ s₁ d₁

          ⟦[⊙]⟧ : (Γ₁ Γ₂ Δ : Con ty) {a σ τ : ty} {B₁ B₂ : Cover a} →
            (E₁ : Cover a) (d₁ : B₁ ≡[ a ]─ E₁) (tm₁ : Γ₁ ++ ｢ E₁ ｣ ++ Δ ⊢ σ)
            (E₂ : Cover a) (d₂ : B₂ ≡[ a ]─ E₂) (tm₂ : Γ₂ ++ ｢ E₂ ｣ ++ Δ ⊢ τ) →
            {B : Cover a} → B ≡ B₁ ⊙ B₂ →
            Σ[ E ∈ Cover a ]
               B ≡[ a ]─ E
             × Γ₁ ++ ｢ E ｣ ++ Δ ⊢ σ
             × Γ₂ ++ ｢ E ｣ ++ Δ ⊢ τ
          ⟦[⊙]⟧ Γ₁ Γ₂ Δ E₁ d₁ tm₁ E₂ d₂ tm₂ (sym s) =
            let (E , d , tm₂ , tm₁) = ⟦[⊙]⟧ Γ₂ Γ₁ Δ E₂ d₂ tm₂ E₁ d₁ tm₁ s
            in E , d , tm₁ , tm₂
          ⟦[⊙]⟧ Γ₁ Γ₂ Δ .(`κ k) (`κ k) tm₁ .(`κ k) (`κ .k) tm₂ (`κ .k) =
            `κ k , `κ k , tm₁ , tm₂
          ⟦[⊙]⟧ Γ₁ Γ₂ Δ (S₁ `⊗ T₁) (prS₁ `⊗ prT₁) tm₁
                       (S₂ `⊗ T₂) (prS₂ `⊗ prT₂) tm₂ (syncl `⊗ syncr) =
            let (E₁ , d₁ , tm₁ , tm₂) =
                  ⟦[⊙]⟧ (Γ₁ ++ ｢ S₁ ｣) (Γ₂ ++ ｢ S₂ ｣) Δ
                        T₁ prT₁ (tm-group⁻¹ Γ₁ ｢ S₁ ｣ ｢ T₁ ｣ Δ tm₁)
                        T₂ prT₂ (tm-group⁻¹ Γ₂ ｢ S₂ ｣ ｢ T₂ ｣ Δ tm₂) syncr
                (E₂ , d₂ , tm₁ , tm₂) =
                  ⟦[⊙]⟧ Γ₁ Γ₂ (｢ E₁ ｣ ++ Δ)
                       S₁ prS₁ (tm-assoc (Γ₁ ++ ｢ S₁ ｣) ｢ E₁ ｣ Δ tm₁)
                       S₂ prS₂ (tm-assoc (Γ₂ ++ ｢ S₂ ｣) ｢ E₁ ｣ Δ tm₂) syncl
            in E₂ `⊗ E₁ , d₂ `⊗ d₁
             , tm-group Γ₁ ｢ E₂ ｣ ｢ E₁ ｣ Δ (tm-assoc⁻¹ (Γ₁ ++ ｢ E₂ ｣) ｢ E₁ ｣ Δ tm₁)
             , tm-group Γ₂ ｢ E₂ ｣ ｢ E₁ ｣ Δ (tm-assoc⁻¹ (Γ₂ ++ ｢ E₂ ｣) ｢ E₁ ｣ Δ tm₂)
          ⟦[⊙]⟧ Γ₁ Γ₂ Δ ._ (prS₁ `⊗[ b ]) tm₁ ._ (prS₂ `⊗[ .b ]) tm₂
            ([ sync ]`⊗ .b) =
            let (E , d , tms) = ⟦[⊙]⟧ Γ₁ Γ₂ Δ _ prS₁ tm₁ _ prS₂ tm₂ sync
            in E `⊗[ b ] , d `⊗[ b ] , tms
          ⟦[⊙]⟧ Γ₁ Γ₂ Δ ._ ([ a ]`⊗ prT₁) tm₁ ._ ([ .a ]`⊗ prT₂) tm₂
            (.a `⊗[ sync ]) =
            let (E , d , tms) = ⟦[⊙]⟧ Γ₁ Γ₂ Δ _ prT₁ tm₁ _ prT₂ tm₂ sync
            in [ a ]`⊗ E , [ a ]`⊗ d , tms
          ⟦[⊙]⟧ Γ₁ Γ₂ Δ .(σ₁ `& b) (σ₁ `& b) tm₁ .(σ₁ `& b) (.σ₁ `& .b) tm₂
            (.σ₁ `& .b) = σ₁ `& b , σ₁ `& b , tm₁ , tm₂
          ⟦[⊙]⟧ Γ₁ Γ₂ Δ ._ (prS `&[ b ]) tm₁ ._ ([ a ]`& prT) tm₂
            ] prA [`&] prB [ =
            let t₁ = ⟦isUsed⟧ Γ₁ Δ (bim prA prS) tm₁
                t₂ = ⟦isUsed⟧ Γ₂ Δ (bim prB prT) tm₂
            in a `& b , a `& b
             , ∈++ˡ Δ zro `&ˡ₁ Eq.subst (flip _⊢_ _) (Eq.sym $ actAt++ˡ Δ zro) t₁
             , ∈++ˡ Δ zro `&ˡ₂ Eq.subst (flip _⊢_ _) (Eq.sym $ actAt++ˡ Δ zro) t₂
          ⟦[⊙]⟧ Γ₁ Γ₂ Δ ._ ([ a ]`& prT) tm₁ .(a `& b) (.a `& b) tm₂
            ] prB [`& =
            let t₁ = ⟦isUsed⟧ Γ₁ Δ (bim prB prT) tm₁
            in a `& b , a `& b
             , ∈++ˡ Δ zro `&ˡ₂ Eq.subst (flip _⊢_ _) (Eq.sym $ actAt++ˡ Δ zro) t₁
             , tm₂
          ⟦[⊙]⟧ Γ₁ Γ₂ Δ ._ (prS `&[ b ]) tm₁ .(a `& b) (a `& .b) tm₂
            `&] prA [ =
            let t₁ = ⟦isUsed⟧ Γ₁ Δ (bim prA prS) tm₁
            in a `& b , a `& b
             , ∈++ˡ Δ zro `&ˡ₁ Eq.subst (flip _⊢_ _) (Eq.sym $ actAt++ˡ Δ zro) t₁
             , tm₂
          ⟦[⊙]⟧ Γ₁ Γ₂ Δ ._ (prS₁ `&[ b ]) tm₁ ._ (prS₂ `&[ .b ]) tm₂
            (sync `&[ .b ]) =
            let (E , d , tms) = ⟦[⊙]⟧ Γ₁ Γ₂ Δ _ prS₁ tm₁ _ prS₂ tm₂ sync
            in E `&[ b ] , d `&[ b ] , tms
          ⟦[⊙]⟧ Γ₁ Γ₂ Δ ._ ([ a ]`& prT₁) tm₁ ._ ([ .a ]`& prT₂) tm₂ 
            ([ .a ]`& sync) =
            let (E , d , tms) = ⟦[⊙]⟧ Γ₁ Γ₂ Δ _ prT₁ tm₁ _ prT₂ tm₂ sync
            in [ a ]`& E , [ a ]`& d , tms

        open Interleaving

        ⟦[]>>=⟧ : {σ : ty} {T U : Cover σ} (Γ₁ Δ₁ Γ₂ Δ₂ : Con ty) {a b : ty}
             (V₁ : Cover σ) (d₁ : T ≡[ σ ]─ V₁) (tm₁ : Γ₁ ++ ｢ V₁ ｣ ++ Δ₁ ⊢ a)
             (V₂ : Cover σ) (d₂ : U ≡ T ─ V₂) (tm₂ : Γ₂ ++ ｢ V₂ ｣ ++ Δ₂ ⊢ b) →
             Σ[ V ∈ Cover σ ] Σ[ S₁ ∈ Con ty ] Σ[ S₂ ∈ Con ty ]
               U ≡[ σ ]─ V × ｢ V ｣ ≡ S₁ ⋈ S₂
             × Γ₁ ++ S₁ ++ Δ₁ ⊢ a × Γ₂ ++ S₂ ++ Δ₂ ⊢ b
        ⟦[]>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ .(`κ k) (`κ k) tm₁ V₂ () tm₂
        ⟦[]>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ (S₁ `⊗ T₁) (prσ `⊗ prτ) tm₁ (S₂ `⊗ T₂) (d₂ `⊗ d₃) tm₂ =
          let tm₁ = tm-group⁻¹ Γ₁ ｢ S₁ ｣ ｢ T₁ ｣ Δ₁ tm₁
              tm₂ = tm-group⁻¹ Γ₂ ｢ S₂ ｣ ｢ T₂ ｣ Δ₂ tm₂
              (T , T₁ , T₂ , dT , jT , tm₁ , tm₂) =
                ⟦[]>>=⟧ (Γ₁ ++ ｢ S₁ ｣) Δ₁ (Γ₂ ++ ｢ S₂ ｣) Δ₂ T₁ prτ tm₁ T₂ d₃ tm₂
              tm₁ = tm-assoc (Γ₁ ++ ｢ S₁ ｣) T₁ Δ₁ tm₁
              tm₂ = tm-assoc (Γ₂ ++ ｢ S₂ ｣) T₂ Δ₂ tm₂
              (S , S₁ , S₂ , dS , jS , tm₁ , tm₂) =
                ⟦[]>>=⟧ Γ₁ (T₁ ++ Δ₁) Γ₂ (T₂ ++ Δ₂) S₁ prσ tm₁ S₂ d₂ tm₂
          in S `⊗ T , S₁ ++ T₁ , S₂ ++ T₂ , dS `⊗ dT , jS Interleaving.++ jT
           , (tm-group Γ₁ S₁ T₁ Δ₁ $ tm-assoc⁻¹ (Γ₁ ++ S₁) T₁ Δ₁ tm₁)
           , (tm-group Γ₂ S₂ T₂ Δ₂ $ tm-assoc⁻¹ (Γ₂ ++ S₂) T₂ Δ₂ tm₂)
        ⟦[]>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ (S₁ `⊗ T₁) (prσ `⊗ prτ) tm₁ (S₂ `⊗[ τ ]) (d₂ `⊗ˡ T) tm₂ =
          let tm₁ = tm-assoc (Γ₁ ++ ｢ S₁ ｣) ｢ T₁ ｣ Δ₁ $
                    tm-group⁻¹ Γ₁ ｢ S₁ ｣ ｢ T₁ ｣ Δ₁ tm₁
              (S , S₁ , S₂ , d , j , tm₁ , tm₂) =
                ⟦[]>>=⟧ Γ₁ (｢ T₁ ｣ ++ Δ₁) Γ₂ Δ₂ S₁ prσ tm₁ S₂ d₂ tm₂
          in S `⊗ T₁ , S₁ ++ ｢ T₁ ｣ , S₂ , d `⊗ prτ , j Interleaving.++ˡ ｢ T₁ ｣
           , (tm-group Γ₁ S₁ ｢ T₁ ｣ Δ₁ $ tm-assoc⁻¹ (Γ₁ ++ S₁) ｢ T₁ ｣ Δ₁ tm₁) , tm₂
        ⟦[]>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ (S₁ `⊗ T₁) (prσ `⊗ prτ) tm₁ ([ σ ]`⊗ T₂) (S `⊗ʳ d₂) tm₂ =
          let tm₁ = tm-group⁻¹ Γ₁ ｢ S₁ ｣ ｢ T₁ ｣ Δ₁ tm₁
              (T , T₁ , T₂ , d , j , tm₁ , tm₂) =
                ⟦[]>>=⟧ (Γ₁ ++ ｢ S₁ ｣) Δ₁ Γ₂ Δ₂ T₁ prτ tm₁ T₂ d₂ tm₂
          in S₁ `⊗ T , ｢ S₁ ｣ ++ T₁ , T₂ , prσ `⊗ d , ｢ S₁ ｣ Interleaving.ˡ++ j
           , tm-group Γ₁ ｢ S₁ ｣ T₁ Δ₁ tm₁ , tm₂
        ⟦[]>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ ([ σ ]`⊗ T₁) ([ .σ ]`⊗ prτ) tm₁
                           ([ .σ ]`⊗ T₂) ([ .σ ]`⊗ d₂) tm₂ =
          let (T , T₁ , T₂ , d , jtms) = ⟦[]>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ T₁ prτ tm₁ T₂ d₂ tm₂
          in [ σ ]`⊗ T , T₁ , T₂ , [ σ ]`⊗ d , jtms
        ⟦[]>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ ([ σ ]`⊗ T₁) ([ .σ ]`⊗ prτ) tm₁
                           (S₂ `⊗[ τ ]) ([ prσ ]`⊗ˡ T) tm₂ =
            S₂ `⊗ T₁ , ｢ T₁ ｣ , ｢ S₂ ｣ , prσ `⊗ prτ
          , ｢ S₂ ｣ Interleaving.ʳ++ˡ ｢ T₁ ｣ , tm₁ , tm₂
        ⟦[]>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ ([ σ ]`⊗ T₁) ([ .σ ]`⊗ prτ) tm₁
                           (S₂ `⊗ T₂) ([ prσ ]`⊗ˡʳ d₂) tm₂ =
          let tm₂ = tm-group⁻¹ Γ₂ ｢ S₂ ｣ ｢ T₂ ｣ Δ₂ tm₂
              (T , T₁ , T₂ , d , j , tm₁ , tm₂) =
                ⟦[]>>=⟧ Γ₁ Δ₁ (Γ₂ ++ ｢ S₂ ｣) Δ₂ T₁ prτ tm₁ T₂ d₂ tm₂
          in S₂ `⊗ T , T₁ , ｢ S₂ ｣ ++ T₂ , prσ `⊗ d , ｢ S₂ ｣ Interleaving.ʳ++ j
           , tm₁ , tm-group Γ₂ ｢ S₂ ｣ T₂ Δ₂ tm₂
        ⟦[]>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ (S₁ `⊗[ τ ]) (prσ `⊗[ .τ ]) tm₁
                           (S₂ `⊗[ .τ ]) (d₂ `⊗[ .τ ]) tm₂ =
          let (S , S₁ , S₂ , d , jtms) = ⟦[]>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ S₁ prσ tm₁ S₂ d₂ tm₂
          in S `⊗[ τ ] , S₁ , S₂ , d `⊗[ τ ] , jtms
        ⟦[]>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ (S₁ `⊗[ τ ]) (prσ `⊗[ .τ ]) tm₁
                           ([ σ ]`⊗ T₂) (S `⊗ʳ[ prτ ]) tm₂ =
            S₁ `⊗ T₂ , ｢ S₁ ｣ , ｢ T₂ ｣ , prσ `⊗ prτ
          , ｢ S₁ ｣ Interleaving.ˡ++ʳ ｢ T₂ ｣ , tm₁ , tm₂
        ⟦[]>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ (S₁ `⊗[ τ ]) (prσ `⊗[ .τ ]) tm₁ 
                            (S₂ `⊗ T₂) (d₂ `⊗ˡʳ[ prτ ]) tm₂ =
          let tm₂ = tm-assoc (Γ₂ ++ ｢ S₂ ｣) ｢ T₂ ｣ Δ₂ $
                    tm-group⁻¹ Γ₂ ｢ S₂ ｣ ｢ T₂ ｣ Δ₂ tm₂
              (S , S₁ , S₂ , d , j , tm₁ , tm₂) =
                ⟦[]>>=⟧ Γ₁ Δ₁ Γ₂ (｢ T₂ ｣ ++ Δ₂) S₁ prσ tm₁ S₂ d₂ tm₂
          in S `⊗ T₂ , S₁ , S₂ ++ ｢ T₂ ｣ , d `⊗ prτ , j Interleaving.++ʳ ｢ T₂ ｣ , tm₁
           , (tm-group Γ₂ S₂ ｢ T₂ ｣ Δ₂ $ tm-assoc⁻¹ (Γ₂ ++ S₂) ｢ T₂ ｣ Δ₂ tm₂)
        ⟦[]>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ .(σ `& τ) (σ `& τ) tm₁ V₂ () tm₂
        ⟦[]>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ ([ σ ]`& T₁) ([ .σ ]`& prT) tm₁
                           ([ .σ ]`& T₂) ([ .σ ]`& d₂) tm₂ =
          let (T , T₁ , T₂ , d , jtms) = ⟦[]>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ T₁ prT tm₁ T₂ d₂ tm₂
          in [ σ ]`& T , T₁ , T₂ , [ σ ]`& d , jtms
        ⟦[]>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ (S₁ `&[ τ ]) (prS `&[ .τ ]) tm₁
                           (S₂ `&[ .τ ]) (d₂ `&[ .τ ]) tm₂ =
          let (S , S₁ , S₂ , d , jtms) = ⟦[]>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ S₁ prS tm₁ S₂ d₂ tm₂
          in S `&[ τ ] , S₁ , S₂ , d `&[ τ ] , jtms

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
                         (S₂ `⊗[ τ ]) ([ prσ ]`⊗ˡ T₂) tm₂ =
           S₂ `⊗ T₁ , ｢ T₁ ｣ , ｢ S₂ ｣ , [ prσ ]`⊗ˡʳ d₁
         , ｢ S₂ ｣ Interleaving.ʳ++ˡ ｢ T₁ ｣ , tm₁ , tm₂
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ ([ .σ ]`⊗ T₁) ([ σ ]`⊗ d₁) tm₁
                         (S₂ `⊗ T₂) ([ prσ ]`⊗ˡʳ d₂) tm₂ =
          let (T , T₁ , T₂ , d , j , tm₁ , tm₂) =
                ⟦>>=⟧ Γ₁ Δ₁ (Γ₂ ++ ｢ S₂ ｣) Δ₂ T₁ d₁ tm₁ T₂ d₂ $
                tm-group⁻¹ Γ₂ ｢ S₂ ｣ ｢ T₂ ｣ Δ₂ tm₂
          in S₂ `⊗ T , T₁ , ｢ S₂ ｣ ++ T₂ , [ prσ ]`⊗ˡʳ d
           , ｢ S₂ ｣ Interleaving.ʳ++ j , tm₁ , tm-group Γ₂ ｢ S₂ ｣ T₂ Δ₂ tm₂
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ ._ (d₁ `⊗[ τ ]) tm₁ ._ (d₂ `⊗[ .τ ]) tm₂ =
          let (S , S₁ , S₂ , d , j , tms) = ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ _ d₁ tm₁ _ d₂ tm₂
          in S `⊗[ τ ] , S₁ , S₂ , d `⊗[ τ ] , j , tms
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ (S₁ `⊗[ .τ ]) (d₁ `⊗[ τ ]) tm₁
                         ([ σ ]`⊗ T₂) (S₂ `⊗ʳ[ prτ ]) tm₂ =
            S₁ `⊗ T₂ , ｢ S₁ ｣ , ｢ T₂ ｣ , d₁ `⊗ˡʳ[ prτ ]
          , ｢ S₁ ｣ Interleaving.ˡ++ʳ ｢ T₂ ｣ , tm₁ , tm₂
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ (S₁ `⊗[ .τ ]) (d₁ `⊗[ τ ]) tm₁
                         (S₂ `⊗ T₂) (d₂ `⊗ˡʳ[ prτ ]) tm₂ =
           let tm₂ = tm-assoc (Γ₂ ++ ｢ S₂ ｣) ｢ T₂ ｣ Δ₂ $
                     tm-group⁻¹ Γ₂ ｢ S₂ ｣ ｢ T₂ ｣ Δ₂ tm₂
               (S , S₁ , S₂ , d , j , tm₁ , tm₂) =
                 ⟦>>=⟧ Γ₁ Δ₁ Γ₂ (｢ T₂ ｣ ++ Δ₂) _ d₁ tm₁ _ d₂ tm₂
           in S `⊗ T₂ , S₁ , S₂ ++ ｢ T₂ ｣ , d `⊗ˡʳ[ prτ ] ,
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
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ (S₁ `⊗[ τ ]) ([ prσ ]`⊗ˡ T) tm₁ (S₂ `⊗ T₂) (d₂ `⊗ d₃) tm₂ =
          let (S , S₁ , S₂ , d , j , tm₁ , tm₂) =
                ⟦[]>>=⟧ Γ₁ Δ₁ Γ₂ (｢ T₂ ｣ ++ Δ₂) S₁ prσ tm₁ S₂ d₂ $
                  tm-assoc (Γ₂ ++ ｢ S₂ ｣) ｢ T₂ ｣ Δ₂ $
                  tm-group⁻¹ Γ₂ ｢ S₂ ｣ ｢ T₂ ｣ Δ₂ tm₂
          in S `⊗ T₂ , S₁ , S₂ ++ ｢ T₂ ｣ , [ d ]`⊗ˡʳ d₃ , j Interleaving.++ʳ ｢ T₂ ｣
           , tm₁ , (tm-group Γ₂ S₂ ｢ T₂ ｣ Δ₂ $ tm-assoc⁻¹ (Γ₂ ++ S₂) ｢ T₂ ｣ Δ₂ tm₂)
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ (S₁ `⊗[ τ ]) ([ prσ ]`⊗ˡ T) tm₁ 
                         (S₂ `⊗[ .τ ]) (d₂ `⊗ˡ .T) tm₂ =
          let (S , S₁ , S₂ , d , j , tms) = ⟦[]>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ S₁ prσ tm₁ S₂ d₂ tm₂
          in S `⊗[ τ ] , S₁ , S₂ , [ d ]`⊗ˡ T , j , tms
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ (S₁ `⊗[ τ ]) ([ prσ ]`⊗ˡ T) tm₁
                         ([ σ ]`⊗ T₂) (S `⊗ʳ d₂) tm₂ =
            S₁ `⊗ T₂ , ｢ S₁ ｣ , ｢ T₂ ｣ , [ prσ ]`⊗ˡʳ d₂
          , ｢ S₁ ｣ Interleaving.ˡ++ʳ ｢ T₂ ｣ , tm₁ , tm₂
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ (S₁ `⊗ T₁) ([ prσ ]`⊗ˡʳ d₁) tm₁ (S₂ `⊗ T₂) (d₂ `⊗ d₃) tm₂ =
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
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ (S₁ `⊗ T₁) ([ prσ ]`⊗ˡʳ d₁) tm₁
                         (S₂ `⊗[ τ ]) (d₂ `⊗ˡ T) tm₂ =
          let tm₁ = tm-assoc (Γ₁ ++ ｢ S₁ ｣) ｢ T₁ ｣ Δ₁ $
                    tm-group⁻¹ Γ₁ ｢ S₁ ｣ ｢ T₁ ｣ Δ₁ tm₁
              (S , S₁ , S₂ , d , j , tm₁ , tm₂) =
                ⟦[]>>=⟧ Γ₁ (｢ T₁ ｣ ++ Δ₁) Γ₂ Δ₂ S₁ prσ tm₁ S₂ d₂ tm₂
          in S `⊗ T₁ , S₁ ++ ｢ T₁ ｣ , S₂ , [ d ]`⊗ˡʳ d₁ , j Interleaving.++ˡ ｢ T₁ ｣
           , (tm-group Γ₁ S₁ ｢ T₁ ｣ Δ₁ $ tm-assoc⁻¹ (Γ₁ ++ S₁) ｢ T₁ ｣ Δ₁ tm₁) , tm₂
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ (S₁ `⊗ T₁) ([ prσ ]`⊗ˡʳ d₁) tm₁
                         ([ σ ]`⊗ T₂) (S `⊗ʳ d₂) tm₂ =
          let tm₁ = tm-group⁻¹ Γ₁ ｢ S₁ ｣ ｢ T₁ ｣ Δ₁ tm₁
              (T , T₁ , T₂ , d , j , tm₁ , tm₂) =
                ⟦>>=⟧ (Γ₁ ++ ｢ S₁ ｣) Δ₁ Γ₂ Δ₂ T₁ d₁ tm₁ T₂ d₂ tm₂
          in S₁ `⊗ T , ｢ S₁ ｣ ++ T₁ , T₂ , [ prσ ]`⊗ˡʳ d
           , ｢ S₁ ｣ Interleaving.ˡ++ j , tm-group Γ₁ ｢ S₁ ｣ T₁ Δ₁ tm₁ , tm₂
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ ([ σ ]`⊗ T₁) (S `⊗ʳ[ prτ ]) tm₁ (S₂ `⊗ T₂) (d₂ `⊗ d₃) tm₂ =
          let tm₂ = tm-group⁻¹ Γ₂ ｢ S₂ ｣ ｢ T₂ ｣ Δ₂ tm₂
              (T , T₁ , T₂ , d , j , tm₁ , tm₂) =
                ⟦[]>>=⟧ Γ₁ Δ₁ (Γ₂ ++ ｢ S₂ ｣) Δ₂ T₁ prτ tm₁ T₂ d₃ tm₂
          in S₂ `⊗ T , T₁ , ｢ S₂ ｣ ++ T₂ , d₂ `⊗ˡʳ[ d ] , ｢ S₂ ｣ Interleaving.ʳ++ j
           , tm₁ , tm-group Γ₂ ｢ S₂ ｣ T₂ Δ₂ tm₂
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ ([ σ ]`⊗ T₁) (S `⊗ʳ[ prτ ]) tm₁
                         (S₂ `⊗[ τ ]) (d₂ `⊗ˡ T) tm₂ =
            S₂ `⊗ T₁ , ｢ T₁ ｣ , ｢ S₂ ｣ , d₂ `⊗ˡʳ[ prτ ]
          , ｢ S₂ ｣ Interleaving.ʳ++ˡ ｢ T₁ ｣ , tm₁ , tm₂
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ ([ σ ]`⊗ T₁) (S `⊗ʳ[ prτ ]) tm₁ ._ (.S `⊗ʳ d₂) tm₂ =
          let (T , T₁ , T₂ , d , jtms) = ⟦[]>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ T₁ prτ tm₁ _ d₂ tm₂
          in [ σ ]`⊗ T , T₁ , T₂ , S `⊗ʳ[ d ] , jtms
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ (S₁ `⊗ T₁) (d₁ `⊗ˡʳ[ prτ ]) tm₁ (S₂ `⊗ T₂) (d₂ `⊗ d₃) tm₂ =
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
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ (S₁ `⊗ T₁) (d₁ `⊗ˡʳ[ prτ ]) tm₁
                         (S₂ `⊗[ τ ]) (d₂ `⊗ˡ T) tm₂ =
          let tm₁ = tm-assoc (Γ₁ ++ ｢ S₁ ｣) ｢ T₁ ｣ Δ₁ $
                    tm-group⁻¹ Γ₁ ｢ S₁ ｣ ｢ T₁ ｣ Δ₁ tm₁
              (S , S₁ , S₂ , d , j , tm₁ , tm₂) = 
                ⟦>>=⟧ Γ₁ (｢ T₁ ｣ ++ Δ₁) Γ₂ Δ₂ S₁ d₁ tm₁ S₂ d₂ tm₂
          in S `⊗ T₁ , S₁ ++ ｢ T₁ ｣ , S₂ , d `⊗ˡʳ[ prτ ] , j Interleaving.++ˡ ｢ T₁ ｣
           , (tm-group Γ₁ S₁ ｢ T₁ ｣ Δ₁ $ tm-assoc⁻¹ (Γ₁ ++ S₁) ｢ T₁ ｣ Δ₁ tm₁) , tm₂
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ (S₁ `⊗ T₁) (d₁ `⊗ˡʳ[ prτ ]) tm₁
                         ([ σ ]`⊗ T₂) (S `⊗ʳ d₂) tm₂ =
          let tm₁ = tm-group⁻¹ Γ₁ ｢ S₁ ｣ ｢ T₁ ｣ Δ₁ tm₁
              (T , T₁ , T₂ , d , j , tm₁ , tm₂) =
                ⟦[]>>=⟧ (Γ₁ ++ ｢ S₁ ｣) Δ₁ Γ₂ Δ₂ T₁ prτ tm₁ T₂ d₂ tm₂
          in S₁ `⊗ T , ｢ S₁ ｣ ++ T₁ , T₂ , d₁ `⊗ˡʳ[ d ] , ｢ S₁ ｣ Interleaving.ˡ++ j
           , tm-group Γ₁ ｢ S₁ ｣ T₁ Δ₁ tm₁ , tm₂

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
        ⟦⊙⟧ Γ₁ Γ₂ Δ .([ a ]) `id tm₁ .([ a ]) `id tm₂ [ a ] = [ a ] , `id , tm₁ , tm₂
        ⟦⊙⟧ Γ₁ Γ₂ Δ ([ a ]) `id tm₁ ._ `id tm₂ ] prA [ rewrite Cover.⟦A⊙A⟧ prA =
         [ a ] , `id , tm₁ , tm₂
        ⟦⊙⟧ Γ₁ Γ₂ Δ ._ [ prS₁ ] tm₁ ._ [ prS₂ ] tm₂ ] prA [ =
          let (S , prS , tms) = Cover.⟦[⊙]⟧ Γ₁ Γ₂ Δ _ prS₁ tm₁ _ prS₂ tm₂ prA
          in ] S [ , [ prS ] , tms
        ⟦⊙⟧ Γ₁ Γ₂ Δ ._ ] prS₁ [ tm₁ ._ ] prS₂ [ tm₂ ] prA [ =
          let (S , prS , tms) = Cover.⟦⊙⟧ Γ₁ Γ₂ Δ _ prS₁ tm₁ _ prS₂ tm₂ prA
          in ] S [ , ] prS [ , tms
        ⟦⊙⟧ Γ₁ Γ₂ Δ ._ `id _ ._ ] prS [ _ ] prA [ = ⊥-elim $ Cover.¬⊙diffˡ prA prS
        ⟦⊙⟧ Γ₁ Γ₂ Δ ._ ] prS [ _ ._ `id _ ] prA [ = ⊥-elim $ Cover.¬⊙diffʳ prA prS

        open Interleaving

        ⟦>>=⟧ : {σ : ty} {S T U : Usage σ} (Γ₁ Δ₁ Γ₂ Δ₂ : Con ty) {a b : ty}
               (V₁ : Usage σ) (d₁ : T ≡ S ─ V₁) (tm₁ : Γ₁ ++ ｢ V₁ ｣ ++ Δ₁ ⊢ a)
               (V₂ : Usage σ) (d₂ : U ≡ T ─ V₂) (tm₂ : Γ₂ ++ ｢ V₂ ｣ ++ Δ₂ ⊢ b) →
               Σ[ V ∈ Usage σ ] Σ[ S₁ ∈ Con ty ] Σ[ S₂ ∈ Con ty ]
                 U ≡ S ─ V × ｢ V ｣ ≡ S₁ ⋈ S₂
               × Γ₁ ++ S₁ ++ Δ₁ ⊢ a × Γ₂ ++ S₂ ++ Δ₂ ⊢ b
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ V₁ d₁ tm₁ ._ `id tm₂ =
          V₁ , ｢ V₁ ｣ , ε , d₁ , reflˡ , tm₁ , tm₂
          where open Interleaving.Interleaving
        ⟦>>=⟧ Γ₁ Δ₁ Γ₂ Δ₂ ._ `id tm₁ V₂ d₂ tm₂ =
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

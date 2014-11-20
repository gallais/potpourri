module poc.internalMuTel where

open import Level using (Level ; Lift ; lift)
open import Data.Bool
open import Data.Nat
open import Data.Fin as Fin
open import Data.Fin.Properties
open import lib.Fin
open import Data.Unit
open import Data.Product
open import Function

data Desc (n : ℕ) : Set₁ where
  `μ : (d : Desc (suc n)) → Desc n
  `r : (k : Fin n) (d : Desc n) → Desc n
  `σ : (A : Set) (d : A → Desc n) → Desc n
  `π : (A : Set) (d : A → Desc n) → Desc n
  `■ : Desc n

tel : ℕ → Set₁
tel zero    = Desc zero
tel (suc n) = tel n × Desc (suc n) 

mutual

  ⟦_⟧ : {n : ℕ} (d : Desc n) (ds : tel n) → Set
  ⟦ `μ d   ⟧ ds = μs (ds , d) zero
  ⟦ `r k d ⟧ ds = μs ds k × ⟦ d ⟧ ds
  ⟦ `σ A d ⟧ ds = Σ[ a ∈ A ] ⟦ d a ⟧ ds
  ⟦ `π A d ⟧ ds = (a : A) → ⟦ d a ⟧ ds
  ⟦ `■     ⟧ ds = ⊤

  data μ {n : ℕ} (d : Desc n) (ds : tel n) : Set where
    ⟨_⟩ : ⟦ d ⟧ ds → μ d ds

  μs : {n : ℕ} (ds : tel n) (k : Fin n) → Set
  μs (ds , d) zero    = μ d (ds , d)
  μs (ds , d) (suc k) = μs ds k

fst : {n : ℕ} (ds : tel n) → Desc zero
fst {0}     = id
fst {suc n} = fst ∘ proj₁

mutual

  fbelow : {n : ℕ} (ds : tel n) (P : μ (fst ds) (fst ds) → Set) (e : Desc n) (v : ⟦ e ⟧ ds) → Set
  fbelow ds P (`μ e)   v       = μbelow ds P e v
  fbelow ds P (`r k e) (r , v) = μsbelow ds P k r × fbelow ds P e v
  fbelow ds P (`σ A d) (a , v) = fbelow ds P (d a) v
  fbelow ds P (`π A d) v       = (a : A) → fbelow ds P (d a) (v a)
  fbelow ds P `■       v       = ⊤

  μbelow : {n : ℕ} (ds : tel n) (P : (v : μ (fst ds) (fst ds)) → Set) (d : Desc $ suc n) (v : μ d (ds , d)) → Set
  μbelow ds P d ⟨ v ⟩ = fbelow (ds , d) P d v

  μsbelow : {n : ℕ} (ds : tel n) (P : (v : μ (fst ds) (fst ds)) → Set) (k : Fin n) (v : μs ds k) → Set
  μsbelow (ds , d) P zero    v = μbelow ds P d v
  μsbelow (ds , d) P (suc k) v = μsbelow ds P k v

mutual

  finduction : {n : ℕ} (ds : tel n) (P : (v : μ (fst ds) (fst ds)) → Set)
               (ih : (v : ⟦ fst ds ⟧ (fst ds)) → fbelow (fst ds) P (fst ds) v → P ⟨ v ⟩)
               (e : Desc n) (v : ⟦ e ⟧ ds) → fbelow ds P e v
  finduction ds P ih (`μ e)   v       = μinduction ds P ih e v
  finduction ds P ih (`r k e) (r , v) = μsinduction ds P ih k r , finduction ds P ih e v
  finduction ds P ih (`σ A d) (a , v) = finduction ds P ih (d a) v
  finduction ds P ih (`π A d) v       = λ a → finduction ds P ih (d a) (v a)
  finduction ds P ih `■       v       = tt

  μinduction : {n : ℕ} (ds : tel n) (P : (v : μ (fst ds) (fst ds)) → Set) 
               (ih : (v : ⟦ fst ds ⟧ (fst ds)) → fbelow (fst ds) P (fst ds) v → P ⟨ v ⟩)
               (d : Desc $ suc n) (v : μ d (ds , d)) → μbelow ds P d v
  μinduction ds P ih d ⟨ v ⟩ = finduction (ds , d) P ih d v

  μsinduction : {n : ℕ} (ds : tel n) (P : (v : μ (fst ds) (fst ds)) → Set)
               (ih : (v : ⟦ fst ds ⟧ (fst ds)) → fbelow (fst ds) P (fst ds) v → P ⟨ v ⟩)
               (k : Fin n) (v : μs ds k) → μsbelow  ds P k v
  μsinduction (ds , d) P ih zero    v = μinduction ds P ih d v
  μsinduction (ds , d) P ih (suc k) v = μsinduction ds P ih k v
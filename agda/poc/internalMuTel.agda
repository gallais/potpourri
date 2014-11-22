module poc.internalMuTel where

open import Level using (Level ; Lift ; lift)
open import Data.Bool
open import Data.Nat
open import Data.Fin as Fin hiding (lift)
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
tel zero    = Lift ⊤
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

tel₁ : {n : ℕ} (ds : tel $ suc n) → tel 1
tel₁ {0}     ds       = ds
tel₁ {suc n} (ds , _) = tel₁ ds

fst : {n : ℕ} (ds : tel $ suc n) → Desc 1
fst = proj₂ ∘ tel₁

mutual

  fbelow : {n : ℕ} (ds : tel $ suc n) (P : μ (fst ds) (tel₁ ds) → Set) (e : Desc $ suc n) (v : ⟦ e ⟧ ds) → Set
  fbelow ds P (`μ e)   v       = μsbelow (ds , e) P zero v
  fbelow ds P (`r k e) (r , v) = μsbelow ds P k r × fbelow ds P e v
  fbelow ds P (`σ A d) (a , v) = fbelow ds P (d a) v
  fbelow ds P (`π A d) v       = (a : A) → fbelow ds P (d a) (v a)
  fbelow ds P `■       v       = ⊤

  μbelow : {n : ℕ} (ds : tel $ suc n) (P : (v : μ (fst ds) (tel₁ ds)) → Set)
           (d : Desc $ suc (suc n)) (v : μ d (ds , d)) → Set
  μbelow ds P d ⟨ v ⟩ = fbelow (ds , d) P d v

  μsbelow : {n : ℕ} (ds : tel $ suc n) (P : (v : μ (fst ds) (tel₁ ds)) → Set)
            (k : Fin $ suc n) (v : μs ds k) → Set
  μsbelow {0}     (ds , d) P zero     v = P v
  μsbelow {suc n} (ds , d) P zero     v = μbelow ds P d v
  μsbelow {0}     (ds , d) P (suc ()) v
  μsbelow {suc n} (ds , d) P (suc k)  v = μsbelow ds P k v

mutual

  finduction : {n : ℕ} (ds : tel $ suc n) (P : (v : μ (fst ds) (tel₁ ds)) → Set)
               (ih : (v : ⟦ fst ds ⟧ (tel₁ ds)) → fbelow (tel₁ ds) P (fst ds) v → P ⟨ v ⟩)
               (e : Desc $ suc n) (v : ⟦ e ⟧ ds) → fbelow ds P e v
  finduction ds P ih (`μ e)   v       = μinduction ds P ih e v
  finduction ds P ih (`r k e) (r , v) = μsinduction ds P ih k r , finduction ds P ih e v
  finduction ds P ih (`σ A d) (a , v) = finduction ds P ih (d a) v
  finduction ds P ih (`π A d) v       = λ a → finduction ds P ih (d a) (v a)
  finduction ds P ih `■       v       = tt

  μinduction : {n : ℕ} (ds : tel $ suc n) (P : (v : μ (fst ds) (tel₁ ds)) → Set) 
               (ih : (v : ⟦ fst ds ⟧ (tel₁ ds)) → fbelow (tel₁ ds) P (fst ds) v → P ⟨ v ⟩)
               (d : Desc $ suc (suc n)) (v : μ d (ds , d)) → μbelow ds P d v
  μinduction ds P ih d ⟨ v ⟩ = finduction (ds , d) P ih d v

  μsinduction : {n : ℕ} (ds : tel $ suc n) (P : (v : μ (fst ds) (tel₁ ds)) → Set)
               (ih : (v : ⟦ fst ds ⟧ (tel₁ ds)) → fbelow (tel₁ ds) P (fst ds) v → P ⟨ v ⟩)
               (k : Fin $ suc n) (v : μs ds k) → μsbelow  ds P k v
  μsinduction {0}     (ds , d) P ih zero     ⟨ v ⟩ = ih v (finduction (ds , d) P ih d v)
  μsinduction {suc n} (ds , d) P ih zero     v     = μinduction ds P ih d v
  μsinduction {0}     (ds , d) P ih (suc ()) v
  μsinduction {suc n} (ds , d) P ih (suc k)  v     = μsinduction ds P ih k v

⟦μ⟧ : Desc 1 → Set
⟦μ⟧ d = μ d (lift tt , d)

induction : (d : Desc 1) (P : ⟦μ⟧ d → Set)
            (ih : (v : ⟦ d ⟧ (lift tt , d)) → fbelow (lift tt , d) P d v → P ⟨ v ⟩) →
            (v : ⟦μ⟧ d) → P v
induction d P ih ⟨ v ⟩ = ih v (finduction (lift tt , d) P ih d v)


natDesc : Desc 1
natDesc = `σ Bool $ λ isZero →
             case isZero of λ
               { true  → `■
               ; false → `r zero `■ }

Zero : ⟦μ⟧ natDesc
Zero = ⟨ true , tt ⟩

Succ : ⟦μ⟧ natDesc → ⟦μ⟧ natDesc
Succ n = ⟨ false , n , tt ⟩

Add : ⟦μ⟧ natDesc → ⟦μ⟧ natDesc → ⟦μ⟧ natDesc
Add m n = induction natDesc P alg m
  where
    P   : ⟦μ⟧ natDesc → Set
    P   = const $ ⟦μ⟧ natDesc
    alg : (v : ⟦ natDesc ⟧ (lift tt , natDesc)) (ih : fbelow (lift tt , natDesc) P natDesc v) → P ⟨ v ⟩
    alg (true  , args) ih       = n
    alg (false , args) (ih , _) = Succ ih

open import Relation.Binary.PropositionalEquality

test : Add (Succ $ Succ Zero) (Succ Zero) ≡ (Succ $ Succ $ Succ Zero)
test = refl

listDesc : {n : ℕ} (k : Fin n) → Desc n
listDesc k =
  `μ $ `σ Bool $ λ isNil →
       case isNil of λ
         { true  → `■
         ; false → `r (suc k) (`r (# 0) `■)
         }

rosetreeDesc : Desc 1
rosetreeDesc = listDesc $ # 0

rosetree : Set
rosetree = ⟦μ⟧ rosetreeDesc

leaf : rosetree
leaf = ⟨ ⟨ true , tt ⟩ ⟩

nil : ⟦ rosetreeDesc ⟧ (lift tt , rosetreeDesc)
nil = ⟨ true , tt ⟩

cons : rosetree → ⟦ rosetreeDesc ⟧ (lift tt , rosetreeDesc) →
                  ⟦ rosetreeDesc ⟧ (lift tt , rosetreeDesc)
cons x xs = ⟨ false , x , xs , tt ⟩


node : ⟦ rosetreeDesc ⟧ (lift tt , rosetreeDesc) → rosetree
node ts = ⟨ ts ⟩

example : rosetree
example = node $ cons t₁ $ cons t₂ nil
  where t₁ : rosetree
        t₁ = node nil
        t₂ : rosetree
        t₂ = node $ cons t₁ $ cons t₁ nil

size : rosetree → ⟦μ⟧ natDesc
size rt = induction rosetreeDesc P alg rt
  where
    P   : rosetree → Set
    P   = const $ ⟦μ⟧ natDesc
    ds  : tel 1
    ds = lift tt , rosetreeDesc
    alg : (v : ⟦ rosetreeDesc ⟧ ds) → fbelow ds P rosetreeDesc v → P ⟨ v ⟩
    -- argh! we would like to do an induction on the list!
    -- the recursive call in alg should not exist!
    alg ⟨ true  , v ⟩          ih           = Zero
    alg ⟨ false , _  , v , _ ⟩ (n , ih , _) = Succ $ Add n $ alg v ih

text′ : size example ≡ (Succ $ Succ $ Succ $ Succ $ Zero)
text′ = refl
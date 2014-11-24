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

prop : {n : ℕ} (d : Desc n) (ds : tel n) → Set₁
prop (`μ d)   ds = prop d (ds , d) × ((v : μs (ds , d) zero) → Set)
prop (`r k d) ds = prop d ds
prop (`σ A d) ds = (a : A) → prop (d a) ds
prop (`π A d) ds = (a : A) → prop (d a) ds
prop `■ ds       = Lift ⊤

props : {n : ℕ} (ds : tel n) → Set₁
props {zero}  ds       = Lift ⊤
props {suc n} (ds , d) = props ds × prop d (ds , d) × ((v : μs (ds , d) zero) → Set)

⟦props⟧ : {n : ℕ} {ds : tel n} (Ps : props ds) (k : Fin n) → μs ds k → Set
⟦props⟧ {zero}  Ps          ()      v
⟦props⟧ {suc n} (_ , _ , P) zero    v = P v
⟦props⟧ {suc n} (Ps , _)    (suc k) v = ⟦props⟧ Ps k v

mutual

  fbelow : {n : ℕ} (ds : tel n) (e : Desc n) (Ps : props ds) (Q : prop e ds)
           (v : ⟦ e ⟧ ds) → Set
  fbelow ds (`μ e)   Ps (Q , P) v      = μbelow ds e (Ps , Q , P) v
  fbelow ds (`r k e) Ps Q      (r , v) = ⟦props⟧ Ps k r × fbelow ds e Ps Q v
  fbelow ds (`σ A e) Ps Q      (a , v) = fbelow ds (e a) Ps (Q a) v
  fbelow ds (`π A e) Ps Q      v       = (a : A) → fbelow ds (e a) Ps (Q a) (v a)
  fbelow ds `■       Ps Q      v       = ⊤

  μbelow : {n : ℕ} (ds : tel n) (e : Desc $ suc n) (Ps : props (ds , e)) (v : μ e (ds , e)) → Set
  μbelow ds e (Ps , Q) v =
    ((v : ⟦ e ⟧ (ds , e)) → fbelow (ds , e) e (Ps , Q) (proj₁ Q) v → proj₂ Q ⟨ v ⟩) → proj₂ Q v

fsbelow : {n : ℕ} (ds : tel n) (Ps : props ds) (k : Fin n) (v : μs ds k) → Set
fsbelow {zero}  ds       Ps           ()      v
fsbelow {suc n} (ds , d) (Ps , Q , P) zero    ⟨ v ⟩ = fbelow (ds , d) d (Ps , Q , P) Q v
fsbelow {suc n} (ds , d) (Ps , Q , P) (suc k) v     = fsbelow ds Ps k v

InductionHyp : {n : ℕ} (ds : tel n) (Ps : props ds) → Set
InductionHyp {n} ds Ps = (k : Fin n) (v : μs ds k) → fsbelow ds Ps k v → ⟦props⟧ Ps k v

mutual

  finduction : {n : ℕ} (ds : tel n) (e : Desc n) (Ps : props ds) (Q : prop e ds)
               (ih : InductionHyp ds Ps) (v : ⟦ e ⟧ ds) → fbelow ds e Ps Q v
  finduction ds (`μ e)   Ps Q ih v       = μinduction ds e Ps Q ih v
  finduction ds (`r k e) Ps Q ih (r , v) = μsinduction ds Ps ih k r , finduction ds e Ps Q ih v
  finduction ds (`σ A d) Ps Q ih (a , v) = finduction ds (d a) Ps (Q a) ih v
  finduction ds (`π A d) Ps Q ih v       = λ a → finduction ds (d a) Ps (Q a) ih (v a)
  finduction ds `■       Ps Q ih v       = tt

  μinduction : {n : ℕ} (ds : tel n) (e : Desc $ suc n) (Ps : props ds) (Q : prop (`μ e) ds)
               (ih : InductionHyp ds Ps) (v : μ e (ds , e)) → μbelow ds e (Ps , Q) v
  μinduction ds e Ps Q ih ⟨ v ⟩ alg = alg v $ finduction (ds , e) e (Ps , Q) (proj₁ Q) (Fin-case knot ih) v
    where knot : (v : μ e (ds , e)) → fsbelow (ds , e) (Ps , Q) zero v → proj₂ Q v
          knot ⟨ v ⟩ ih = alg v ih

  μsinduction : {n : ℕ} (ds : tel n) (Ps : props ds)
                (ih : InductionHyp ds Ps) (k : Fin n) (v : μs ds k) → ⟦props⟧ Ps k v
  μsinduction (ds , d) (Ps , P) ih zero v = μinduction ds d Ps P (ih ∘ suc) v (ih zero ∘ ⟨_⟩)
  μsinduction (ds , _) (Ps , _) ih (suc k) v = μsinduction ds Ps (ih ∘ suc) k v


-- EXAMPLE

⟦_⟧0 : Desc 0 → Set
⟦_⟧0 d = ⟦ d ⟧ (lift tt)

natDesc : {n : ℕ} → Desc $ suc n
natDesc = `σ Bool $ λ isZero →
             case isZero of λ
               { true  → `■
               ; false → `r zero `■ }

⟦nat⟧ : Set
⟦nat⟧ = ⟦ `μ natDesc ⟧0

Zero : {n : ℕ} {ds : tel n} → μ natDesc (ds , natDesc)
Zero = ⟨ true , tt ⟩

Succ : {n : ℕ} {ds : tel n} → μ natDesc (ds , _) → μ natDesc (ds , _)
Succ n = ⟨ false , n , tt ⟩

Bool-case : {ℓ : Level} {P : Bool → Set ℓ} (Pt : P true) (Pf : P false) (b : Bool) → P b
Bool-case Pt Pf true  = Pt
Bool-case Pt Pf false = Pf

Add : ⟦nat⟧ → ⟦nat⟧ → ⟦nat⟧
Add m n = μinduction (lift tt) natDesc (lift tt) P (λ ()) m alg
  where
    P : prop (`μ natDesc) (lift tt)
    P = Bool-case (lift tt) (lift tt) , const ⟦nat⟧
    alg : (v : ⟦ natDesc ⟧ (lift tt , natDesc)) →
          fbelow (lift tt , natDesc) natDesc (lift tt , P) (proj₁ P) v →
          proj₂ P ⟨ v ⟩
    alg (true  , _) _        = n
    alg (false , _) (ih , _) = Succ ih

open import Relation.Binary.PropositionalEquality

test : Add (Succ $ Succ Zero) (Succ Zero) ≡ (Succ $ Succ $ Succ Zero)
test = refl

listDesc : {n : ℕ} (k : Fin n) → Desc (suc n)
listDesc k =
       `σ Bool $ λ isNil →
       case isNil of λ
         { true  → `■
         ; false → `r (suc k) (`r (# 0) `■)
         }

rosetreeDesc : Desc 1
rosetreeDesc =
       `σ Bool $ λ isLeaf →
        case isLeaf of λ
          { true  → `μ natDesc
          ; false → `μ $ listDesc $ # 0 }

rosetree : Set
rosetree = ⟦ `μ rosetreeDesc ⟧0

rosetrees : Set
rosetrees = μ (listDesc $ # 0) ((lift tt , rosetreeDesc) , listDesc (# 0))

leaf : μ natDesc _ → rosetree
leaf n = ⟨ true , n ⟩

nil : rosetrees
nil = ⟨ true , tt ⟩

cons : rosetree → rosetrees → rosetrees
cons x xs = ⟨ false , x , xs , tt ⟩

node : μ (listDesc $ # 0) ((lift tt , rosetreeDesc) , listDesc (# 0))  → rosetree
node ts = ⟨ false , ts ⟩

example : rosetree
example = node $ cons t₁ $ cons t₃ nil
  where t₁ : rosetree
        t₁ = leaf $ Succ $ Succ Zero
        t₂ : rosetree
        t₂ = leaf $ Succ Zero
        t₃ : rosetree
        t₃ = node $ cons t₂ $ cons t₂ nil

size : rosetree → ⟦nat⟧
size rt = μinduction (lift tt) rosetreeDesc (lift tt) (Q , P) (λ ()) rt alg
  where
    P   : {A : Set} (a : A) → Set
    P   = const ⟦nat⟧
    Q   : prop rosetreeDesc (lift tt , rosetreeDesc)
    Q   = Bool-case (Bool-case (lift tt) (lift tt) , const ⊤) (Bool-case (lift tt) (lift tt) , const ⟦nat⟧)
    ds  : tel 2
    ds = (lift tt , rosetreeDesc) , listDesc (# 0)
    alg′ : (v : ⟦ listDesc (# 0) ⟧ ds)
           (ih : fbelow ds (listDesc (# 0)) _ (Bool-case (lift tt) (lift tt)) v) →
           ⟦nat⟧
    alg′ (true  , v) ih                      = Zero
    alg′ (false , v) (size-r , size-rs , tt) = Add size-r size-rs
    alg : (v : ⟦ rosetreeDesc ⟧ (lift tt , rosetreeDesc))
          (ih : fbelow (lift tt , rosetreeDesc) rosetreeDesc (lift tt , Q , P) Q v) →
          ⟦nat⟧
    alg (true  , _) _  = Succ Zero
    alg (false , _) ih = ih alg′

test′ : size example ≡ (Succ $ Succ $ Succ $ Zero)
test′ = refl

open import Data.List

leaves : rosetree → List $ μ natDesc ((lift tt , rosetreeDesc) , natDesc)
leaves rt = μinduction (lift tt) rosetreeDesc (lift tt) (Q , P) (λ ()) rt alg
  where
    Res : Set
    Res = List $ μ natDesc ((lift tt , rosetreeDesc) , natDesc)
    P   : {A : Set} (a : A) → Set
    P   = const Res
    Q   : prop rosetreeDesc (lift tt , rosetreeDesc)
    Q   = Bool-case (Bool-case (lift tt) (lift tt) , const ⊤) (Bool-case (lift tt) (lift tt) , const Res)
    ds  : tel 2
    ds = (lift tt , rosetreeDesc) , listDesc (# 0)
    alg′ : (v : ⟦ listDesc (# 0) ⟧ ds)
           (ih : fbelow ds (listDesc (# 0)) _ (Bool-case (lift tt) (lift tt)) v) →
           Res
    alg′ (true  , v) ih                      = []
    alg′ (false , v) (leaves , leavess , tt) = leaves ++ leavess
    alg : (v : ⟦ rosetreeDesc ⟧ (lift tt , rosetreeDesc))
          (ih : fbelow (lift tt , rosetreeDesc) rosetreeDesc (lift tt , Q , P) Q v) →
          Res
    alg (true  , v) _  = v ∷ []
    alg (false , _) ih = ih alg′

test′′ :
  let `1 = Succ Zero
      `2 = Succ `1
  in leaves example ≡ `2 ∷ `1 ∷ `1 ∷ []
test′′ = refl
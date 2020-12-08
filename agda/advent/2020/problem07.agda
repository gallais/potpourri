module problem07 where

open import Data.Bool.Base as Bool using (if_then_else_)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; _*_)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_; uncurry; proj₁)
open import Data.String.Base as String using (String)
import Data.String.Properties as Stringₚ
open import Function.Base

record Bag : Set where
  constructor MkBag
  field adjective : String
        color     : String

toPair : Bag → String × String
toPair (MkBag b₁ b₂) = (b₁ , b₂)

open import lib

rule : List String → Maybe (Bag × List (ℕ × Bag))
rule (b₁ ∷ b₂ ∷ "bags" ∷ "contain" ∷ "no" ∷ "other" ∷ "bags." ∷ []) = just (MkBag b₁ b₂ , [])
rule (b₁ ∷ b₂ ∷ "bags" ∷ "contain" ∷ rest)
  = just (MkBag b₁ b₂ , payloads rest) where

  payloads : List String → List (ℕ × Bag)
  payloads (n ∷ b₁ ∷ b₂ ∷ _ ∷ rest) =
    (Maybe.fromMaybe 0 (readMaybe n) , MkBag b₁ b₂) ∷ payloads rest
  payloads _ = []
rule ws = nothing

open import Data.Product.Relation.Binary.Lex.Strict using (×-strictTotalOrder)
bag-strictTotalOrder = ×-strictTotalOrder Stringₚ.<-strictTotalOrder-≈ Stringₚ.<-strictTotalOrder-≈

import Data.Tree.AVL.Map Stringₚ.<-strictTotalOrder-≈ as Map1 -- for part 1
import Data.Tree.AVL.Map bag-strictTotalOrder         as Map2 -- for part 2

open import Data.Tree.AVL.Sets bag-strictTotalOrder as Sets using (⟨Set⟩)

Rules1 = Map1.Map (Map1.Map ⟨Set⟩)
Rules2 = Map2.Map (Map2.Map ℕ)

record Rules : Set where
  constructor MkRules
  field backwards : Rules1
        forwards  : Rules2

rules : List String → Rules
rules = List.foldr steps (MkRules Map1.empty Map2.empty) where

  step1 : Bag → (ℕ × Bag) → Rules1 → Rules1
  step1 b (_ , MkBag b₁ b₂) = Map1.insertWith b₁ $ λ where
    nothing  → Map1.singleton b₂ (Sets.singleton (toPair b))
    (just r) → Map1.insertWith b₂ (Sets.insert (toPair b) ∘′ Maybe.fromMaybe Sets.empty) r

  step2 : Bag → (ℕ × Bag) → Rules2 → Rules2
  step2 b (n , target) = Map2.insertWith (toPair b) $ λ where
    nothing  → Map2.singleton (toPair target) n
    (just r) → Map2.insert (toPair target) n r

  step : Bag → List (ℕ × Bag) → Rules → Rules
  step b bs (MkRules rules1 rules2) =
    let rules2 = Map2.insertWith (toPair b) (Maybe.fromMaybe Map2.empty) rules2 in
    MkRules (List.foldr (step1 b) rules1 bs)
            (List.foldr (step2 b) rules2 bs)

  steps : String → Rules → Rules
  steps str acc = case rule (String.words str) of λ where
    nothing         → acc
    (just (b , bs)) → step b bs acc

reachable : ℕ → Bag → Rules1 → ⟨Set⟩
reachable n b rules = go n (Sets.singleton (toPair b)) Sets.empty Sets.empty where

  go : ℕ → ⟨Set⟩ → ⟨Set⟩ → ⟨Set⟩ → ⟨Set⟩
  go zero    queue visited acc = acc
  go (suc n) queue visited acc = case Sets.headTail queue of λ where
    nothing → acc
    (just (b@(b₁ , b₂) , queue)) →
      if b Sets.∈? visited then go n queue visited acc else
      let bags = Map1.lookup b₁ rules Maybe.>>= Map1.lookup b₂ in
      let next = Sets.toList (Maybe.fromMaybe Sets.empty bags) in
      let queue = List.foldr Sets.insert queue next in
      let acc = List.foldr Sets.insert acc next in
      go n queue (Sets.insert b visited) acc

open import Category.Monad.State
open import Data.Unit
open import Data.List.Categorical as List

cost : ℕ → Bag → Rules2 → ℕ
cost n b rules = ℕ.pred $ proj₁ $ full Map2.empty where

  open RawMonadState (StateMonadState (Map2.Map ℕ))

  M = State (Map2.Map ℕ)

  check : String × String → M (Maybe ℕ)
  check b@(b₁ , b₂) = do
    m ← get
    return (Map2.lookup b m)

  go : ℕ → ⟨Set⟩ → M ⊤
  go zero    queue = return _
  go (suc n) queue = case Sets.headTail queue of λ where
    nothing → return _
    (just (b , queue)) → do
      visited ← check b
      case visited of λ where
        (just _) → go n queue
        nothing → case Map2.lookup b rules of λ where
          nothing → do modify (Map2.insert b 0)
                       go n queue
          (just m) → do let next = Map2.toList m
                        go n (Sets.fromList (List.map proj₁ next))
                        let cost = λ (b , n) → (n *_) ∘′ Maybe.fromMaybe 0 <$> check b
                        vs ← TraversableM.mapM (StateMonad _) cost next
                        modify (Map2.insert b (suc (List.sum vs)))
                        go n queue

  full : M ℕ
  full = do
    let b = toPair b
    go n (Sets.singleton b)
    Maybe.fromMaybe 0 <$> check b


measure : ℕ → Bag → Rules → ℕ
measure n b rules =
  let candidates = reachable n b (Rules.backwards rules) in
  List.length (Sets.toList candidates)

open import IO
open import lib

main = run $ do
  content ← String.lines <$> getInput
  let n = suc (List.length content)
  let rules = rules content
  let bag = MkBag "shiny" "gold"
  putStrLn $ show $ measure n bag rules
  putStrLn $ show $ cost n bag (Rules.forwards rules)

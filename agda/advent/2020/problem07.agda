module problem07 where

open import Data.Bool.Base as Bool using (if_then_else_)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_; uncurry)
open import Data.String.Base as String using (String)
import Data.String.Properties as Stringₚ
open import Function.Base

record Bag : Set where
  constructor MkBag
  field adjective : String
        color     : String

toPair : Bag → String × String
toPair (MkBag b₁ b₂) = (b₁ , b₂)

rule : List String → Maybe (Bag × List Bag)
rule (_ ∷ _ ∷ "bags" ∷ "contain" ∷ "no" ∷ "other" ∷ "bags." ∷ []) = nothing
rule (b₁ ∷ b₂ ∷ "bags" ∷ "contain" ∷ rest)
  = just (MkBag b₁ b₂ , payloads rest) where

  payloads : List String → List Bag
  payloads (_ ∷ b₁ ∷ b₂ ∷ _ ∷ rest) = MkBag b₁ b₂ ∷ payloads rest
  payloads _ = []
rule _ = nothing

open import lib
open import Data.Tree.AVL.Map Stringₚ.<-strictTotalOrder-≈ as Map using (Map)

open import Data.Product.Relation.Binary.Lex.Strict using (×-strictTotalOrder)
bag-strictTotalOrder = ×-strictTotalOrder Stringₚ.<-strictTotalOrder-≈ Stringₚ.<-strictTotalOrder-≈

open import Data.Tree.AVL.Sets bag-strictTotalOrder as Sets using (⟨Set⟩)

Rules : Set
Rules = Map (Map ⟨Set⟩)

rules : List String → Rules
rules = List.foldr steps Map.empty where

  step : Bag → Bag → Rules → Rules
  step b (MkBag b₁ b₂) = Map.insertWith b₁ $ λ where
    nothing  → Map.singleton b₂ (Sets.singleton (toPair b))
    (just r) → Map.insertWith b₂ (Sets.insert (toPair b) ∘′ Maybe.fromMaybe Sets.empty) r

  steps : String → Rules → Rules
  steps str acc = case rule (String.words str) of λ where
    nothing         → acc
    (just (b , bs)) → List.foldr (step b) acc bs

reachable : ℕ → Bag → Rules → ⟨Set⟩
reachable n b rules = go n (Sets.singleton (toPair b)) Sets.empty Sets.empty where

  go : ℕ → ⟨Set⟩ → ⟨Set⟩ → ⟨Set⟩ → ⟨Set⟩
  go zero    queue visited acc = acc
  go (suc n) queue visited acc = case Sets.headTail queue of λ where
    nothing → acc
    (just (b@(b₁ , b₂) , queue)) →
      if b Sets.∈? visited then go n queue visited acc else
      let bags = Map.lookup b₁ rules Maybe.>>= Map.lookup b₂ in
      let next = Sets.toList (Maybe.fromMaybe Sets.empty bags) in
      let queue = List.foldr Sets.insert queue next in
      let acc = List.foldr Sets.insert acc next in
      go n queue (Sets.insert b visited) acc

measure : Bag → List String → ℕ
measure b lines =
  let n = suc (List.length lines) in
  let rules = rules lines in
  let candidates = reachable n b rules in
  List.length (Sets.toList candidates)

open import IO

main = run $ do
  content ← String.lines <$> getInput
  putStrLn $ show $ measure (MkBag "shiny" "gold") content

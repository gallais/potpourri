module problem11 where

open import Codata.Delay as Delay using (Delay)
open import Codata.Thunk using (force)
open import Data.Bool.Base using (false; if_then_else_; _∧_; _∨_; not)
open import Data.Char.Base using (Char)
open import Data.List.Base as List using (List; []; _∷_; _++_)
open import Data.Maybe.Base using (is-just)
open import Data.Nat.Base as ℕ using (ℕ; _≡ᵇ_; _<ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Integer.Base as ℤ using (ℤ; suc; pred; +_)
open import Data.Integer.Properties as ℤₚ using (_≟_)
open import Data.Product using (_×_; _,_)
open import Data.Product.Relation.Binary.Lex.Strict using (×-strictTotalOrder)
open import Data.String.Base as String using (String; lines)
open import Data.Sum.Base as Sum using (inj₁; inj₂)
open import Data.These.Base as These using (These)
open import Data.Unit using (tt)
open import Function.Base

open import Relation.Nullary using (does)

<-pairs = ×-strictTotalOrder ℤₚ.<-strictTotalOrder ℤₚ.<-strictTotalOrder
open import Data.Tree.AVL.Sets <-pairs as Sets using (⟨Set⟩; _∈?_)

record Layout : Set where
  constructor MkLayout
  field seats    : ⟨Set⟩
        occupied : ⟨Set⟩

initLayout : List String → Layout
initLayout ls = record
  { seats    = initLines ls 0 Sets.empty
  ; occupied = Sets.empty
  } where

    initLine : List Char → ℕ → ℕ → ⟨Set⟩ → ⟨Set⟩
    initLine []         i j = id
    initLine ('L' ∷ cs) i j = initLine cs i (ℕ.suc j) ∘′ Sets.insert (+ i , + j)
    initLine (_   ∷ cs) i j = initLine cs i (ℕ.suc j)

    initLines : List String → ℕ → ⟨Set⟩ → ⟨Set⟩
    initLines []       i = id
    initLines (l ∷ ls) i = initLines ls (ℕ.suc i) ∘′ initLine (String.toList l) i 0

open import lib

step : Layout → Layout
step (MkLayout seats occupied) = MkLayout seats occupied' where

  neighbours : (ℤ × ℤ) → List (ℤ × ℤ)
  neighbours (i , j) = List.map (pred i ,_) (pred j ∷ j ∷ suc j ∷ [])
                    ++ List.map (i ,_)      (pred j     ∷ suc j ∷ [])
                    ++ List.map (suc i ,_)  (pred j ∷ j ∷ suc j ∷ [])

  evolve : (ℤ × ℤ) → ⟨Set⟩ → ⟨Set⟩
  evolve pt =
    let isTaken = pt ∈? occupied in
    let neighbours = List.sum (List.mapMaybe (λ ij → when (ij ∈? occupied) 1) (neighbours pt)) in
    if (not isTaken ∧ (neighbours ≡ᵇ 0)) ∨ (isTaken ∧ (neighbours <ᵇ 4))
    then Sets.insert pt else id

  occupied' : ⟨Set⟩
  occupied' = Sets.foldr evolve Sets.empty seats

lifecycle : Layout → Delay Layout _
lifecycle = Delay.unfold $ λ l →
  let l'     = step l
      occ    = Sets.toList (Layout.occupied l)
      occ'   = Sets.toList (Layout.occupied l')
      check  = These.fold (const false) (const false)
               λ (i , j) (i' , j') → does (i ≟ i') ∧ does (j ≟ j')
      checks = List.alignWith check occ occ'
  in if List.and checks
  then inj₂ l'
  else inj₁ l'

open import Codata.Musical.Notation
open import IO

wait : Delay Layout _ → IO Layout
wait (Delay.now l)    = pure l
wait (Delay.later dl) = seq (♯ pure tt) (♯ wait (dl .force))

main = run $ do
  lines  ← lines <$> getInput
  layout ← wait (lifecycle (initLayout lines))
  putStrLn $ show $ Sets.size (Layout.occupied layout)

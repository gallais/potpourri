module problem05 where

open import Level using (0ℓ)
open import Data.Bool.Base using (if_then_else_; _∧_)
open import Data.List.Base as List using (List)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_)
import Data.Nat.Properties as ℕₚ
open import Data.Nat.Show using (show)
open import Data.Product using (uncurry)
open import Data.String.Base as String using (String)
open import Data.Sum using (isInj₂)
open import Data.Vec.Base as Vec using (Vec; _∷_; [])
open import Function.Base

open import Relation.Unary
open import Text.Parser 0ℓ as Combinators using (runParser)

convert : ∀ {n} → Vec ℕ n → ℕ
convert = Vec.foldl (const ℕ) (λ acc r → r + 2 * acc) 0

data RowSplit : Set where F B : RowSplit
data ColSplit : Set where L R : ColSplit

record Seat : Set where
  constructor MkSeat
  field rowSplit : Vec RowSplit 7
        colSplit : Vec ColSplit 3

rowSplit : RowSplit → ℕ
rowSplit F = 0
rowSplit B = 1

colSplit : ColSplit → ℕ
colSplit L = 0
colSplit R = 1

pickRow : Vec RowSplit 7 → ℕ
pickRow = convert ∘′ Vec.map rowSplit

pickCol : Vec ColSplit 3 → ℕ
pickCol = convert ∘′ Vec.map colSplit

seatID : Seat → ℕ
seatID s = 8 * pickRow (Seat.rowSplit s) + pickCol (Seat.colSplit s)

module _ where

  open Combinators

  parseRowSplit : ∀[ Parser [ Vec RowSplit 7 ] ]
  parseRowSplit = replicate 7 ((F <$ char 'F') <|> (B <$ char 'B'))

  parseColSplit : ∀[ Parser [ Vec ColSplit 3 ] ]
  parseColSplit = replicate 3 ((L <$ char 'L') <|> (R <$ char 'R'))

  parseSeat : ∀[ Parser [ Seat ] ]
  parseSeat = uncurry MkSeat <$> (parseRowSplit <&> box parseColSplit)

open import Data.List.Extrema ℕₚ.≤-totalOrder using (max)
open import Data.Tree.AVL.Sets ℕₚ.<-strictTotalOrder as Sets using (⟨Set⟩; _∈?_)

findSeat : List ℕ → ℕ
findSeat seatIDs = go 1015 where

  seats : ⟨Set⟩
  seats = Sets.fromList seatIDs

  go : ℕ → ℕ
  go zero    = 0
  go (suc n) =
    if suc n ∈? seats then go n else
      (if (n ∈? seats) ∧ ((2 + n) ∈? seats) then suc n else go n)

open import IO
open import lib

main = run $ do
  lines ← String.lines <$> getInput
  let seats = List.mapMaybe (isInj₂ ∘′ runParser parseSeat) lines
  let seatIDs = List.map seatID seats
  putStrLn $ show (max 0 seatIDs)
  putStrLn $ show (findSeat seatIDs)

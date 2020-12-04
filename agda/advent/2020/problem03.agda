module problem03 where

open import Data.Bool.Base as Bool using (Bool; true; false; if_then_else_)
open import Data.Char.Base as Char using (Char)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.Maybe.Base as Maybe using (nothing; just; maybe′)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; _+_; _∸_)
open import Data.Nat.DivMod using (_%_)
import Data.Nat.Properties as ℕₚ
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_)
open import Data.String.Base as String using (String)
open import Data.Tree.AVL.Map ℕₚ.<-strictTotalOrder as Map using (Map)
open import Data.Unit.Base using (⊤)
open import Function.Base
open import Strict

record Terrain : Set where
  constructor MkTerrain
  field width   : ℕ
        height  : ℕ
        terrain : Map (Map ⊤)

readTerrain : List String → Terrain
readTerrain lines = MkTerrain (ℕ.pred width) height (gos 0 lines Map.empty) where

  width = maybe′ String.length 0 (List.head lines)
  height = List.length lines

  go : ℕ → ℕ → List Char → Map (Map ⊤) → Map (Map ⊤)
  go ln cn []         m = m
  go ln cn ('#' ∷ cs) m =
    let m′ = Map.insertWith ln (maybe′ (Map.insert cn _) (Map.singleton cn _)) m
    in force m′ (go ln (suc cn) cs)
  go ln cn (_   ∷ cs) m = go ln (suc cn) cs m

  gos : ℕ → List String → Map (Map ⊤) → Map (Map ⊤)
  gos ln []         m = m
  gos ln (cs ∷ css) m =
    let m′ = go ln 0 (String.toList cs) m
    in force m′ (gos (suc ln) css)

check : Terrain → (ℕ × ℕ) → ℕ
check t (right , down) = go height 0 height 0 0 where

  open Terrain t

  hasTree : ℕ → ℕ → Bool
  hasTree i j = case Map.lookup i terrain of λ where
    nothing     → false
    (just line) → case Map.lookup j line of λ where
      nothing  → false
      (just _) → true

  go : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  -- if either the measure or the height is 0: return the accumulator
  go 0 acc _ _ _ = acc
  go _ acc 0 _ _ = acc
  -- otherwise: proceed
  go (suc measure) acc h i j =
    let acc′ = if hasTree i j then suc acc else acc
    in seq acc′ (go measure acc′ (h ∸ down) (i + down) ((j + right) % suc width))

open import IO
open import System.Environment

getInput : IO String
getInput = do
  args ← getArgs
  (just fp) ← pure (List.head args)
    where _ → pure ""
  readFiniteFile fp

showTest : (ℕ × ℕ) → ℕ → String
showTest (right , down) trees = let open String hiding (show) in
  "(" ++ show right ++ ":" ++ show down ++ ") = " ++ show trees

main = run $ do
  content ← String.lines <$> getInput
  let terrain = readTerrain content
  let tests   = ((1 , 1) ∷ (3 , 1) ∷ (5 , 1) ∷ (7 , 1) ∷ (1 , 2) ∷ [])
  let results = List.map (check terrain) tests
  List.mapM′ putStrLn (List.zipWith showTest tests results)
  putStrLn $ show $ List.product results

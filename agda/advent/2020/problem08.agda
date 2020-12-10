module problem08 where

open import Level using (0ℓ)
open import Data.Bool.Base using (true; false)
open import Data.Integer.Base
open import Data.List.Base as List using (List; _∷_; [])
import Data.List.NonEmpty as List⁺
open import Data.List.Zipper as Zipper using (Zipper)
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just; maybe′)
open import Data.Nat.Base as ℕ using (ℕ; suc)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (_×_; _,_; uncurry)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Function.Base

open import Relation.Unary
import Text.Parser

data Operation : Set where
  ACC JMP NOP : Operation

record Instruction : Set where
  constructor _∙_
  field operation : Operation
        argument  : ℤ

record Machine : Set where
  constructor [_,_]_
  field ipointer : ℕ
        accumulator : ℤ
        code : Zipper Instruction

getInstruction : Machine → Maybe Instruction
getInstruction = List.head ∘′ Zipper.value ∘′ Machine.code

initMachine : List Instruction → Machine
initMachine code = [ 0 , + 0 ] (Zipper.fromList code)

module _ where

  open Text.Parser 0ℓ

  operation : ∀[ Parser [ Operation ] ]
  operation = alts $ (ACC <$ text "acc")
                   ∷ (JMP <$ text "jmp")
                   ∷ (NOP <$ text "nop")
                   ∷ []

  instruction : ∀[ Parser [ Instruction ] ]
  instruction = uncurry _∙_ <$> (operation <&> box (withSpaces decimalℤ))

  machine : ∀[ Parser [ Machine ] ]
  machine = (initMachine ∘′ List⁺.toList) <$> list⁺ instruction

  parse = runParserIO machine

jmp : ℤ → Zipper Instruction → Maybe (Zipper Instruction)
jmp (+ 0)        zp = just zp
jmp +[1+ n     ] zp = Zipper.right zp Maybe.>>= jmp (+ n)
jmp -[1+ 0     ] zp = Zipper.left zp
jmp -[1+ suc n ] zp = Zipper.left zp Maybe.>>= jmp -[1+ n ]

next : Zipper Instruction → Maybe (Zipper Instruction)
next = jmp (+ 1)

infixr 5 _⊕_
_⊕_ : ℕ → ℤ → ℕ
m ⊕ + n      = m ℕ.+ n
m ⊕ -[1+ n ] = m ℕ.∸ ℕ.suc n

step : Instruction → Machine → Maybe Machine
step (NOP ∙ arg) ([ ip , acc ] code) = Maybe.map [ ℕ.suc ip , acc       ]_ (next code)
step (ACC ∙ arg) ([ ip , acc ] code) = Maybe.map [ ℕ.suc ip , acc + arg ]_ (next code)
step (JMP ∙ arg) ([ ip , acc ] code) = Maybe.map [ ip ⊕ arg , acc       ]_ (jmp arg code)


open import Codata.Cowriter using (Cowriter; unfold)
open import Codata.Thunk using (force)

execute : Machine → Cowriter Machine ℤ _
execute = unfold $ let _>>=_ = Maybe._>>=_ in λ where
  m → maybe′ inj₁ (inj₂ (Machine.accumulator m))
    $ do instr ← getInstruction m
         m     ← step instr m
         just (m , m)

open import Size using (∞)
open import Codata.Musical.Notation using (♯_)
open import IO
open import Data.Tree.AVL.Sets ℕₚ.<-strictTotalOrder as Sets using (⟨Set⟩)

loopy : Machine → IO ((ℕ × ℤ) ⊎ ℤ)
loopy m = Sum.map₁ finish <$> go Sets.empty m (execute m) where

  finish : Machine → ℕ × ℤ
  finish ([ ip , acc ] _) = ip , acc

  open Cowriter

  go : ⟨Set⟩ → Machine → Cowriter Machine ℤ ∞ → IO (Machine ⊎ ℤ)
  go visited m   [ z ]    = pure (inj₂ z)
  go visited old (m ∷ ms) with ip ← Machine.ipointer m | ip Sets.∈? visited
  ... | true  = pure (inj₁ old)
  ... | false = bind (♯ go (Sets.insert ip visited) m (ms .force)) (λ x → ♯ pure x)

open import lib

main = run $ do
  input ← getInput
  m ← parse input
  acc ← loopy m
  case acc of λ where
    (inj₁ (_ , acc)) → putStrLn $ showℤ acc
    (inj₂ _) → putStrLn "No loop!"

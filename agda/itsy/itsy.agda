module itsy where

open import Data.Nat.Base  using (ℕ; zero; suc; _+_)   -- Natural numbers: 0,1,2, ...
open import Data.List.Base using (List; []; _∷_; _++_) -- Finite lists, we only use lists of natural numbers here
open import Data.Vec.Base  using (Vec; []; _∷_)        -- Vectors aka lists of a specific length
open import Data.Product   using (_×_ ; _,_; ∃; proj₁) -- Pairs of values of different types
open import Relation.Binary.PropositionalEquality      -- A notion of equality
  using (_≡_) renaming (refl to trivial)

----------------------------------------------------------------
-- An ITSY machine
----------------------------------------------------------------

-- We introduce an extremely simplified version of the TINY machine.
-- It has no flag register, no loop index, no input queue, and way
-- fewer instructions in its assembly language.

-- In our idealised setting we also do not worry about actually
-- storing the code into memory and having an instruction pointer.

----------------------------------------------------------------
-- The state of an ITSY machine
----------------------------------------------------------------

-- We model the state of the ITSY machine as a record (i.e. a
-- collection of different values labelled by a name) containing:
--
-- * AC   the value of its accumulator
-- * MEM  the value contained in the 4 locations of its memory

-- All of these values are natural numbers. This means that, unlike
-- with TINY, we do not have to worry about overflows, carries, etc:
-- all the operations will succeed.

infix 5 _<_>
record ITSY : Set where
  constructor _<_>
  field AC  : ℕ
        MEM : Vec ℕ 4
open ITSY

-- We can give some examples of memory and ITSY configurations

mem : Vec ℕ 4
mem = 0 ∷ 1 ∷ 2 ∷ 3 ∷ []

itsy : ITSY
itsy = 0 < mem >

-- NB: the constructor _<_> was declared in the definition of ITSY,
-- it takes a value for the accumulator and a memory configuration
-- and builds an ITSY machine.

-- To refer to memory locations, we need a notion of addresses.
-- Here we declare ADDR a type with 4 different values corresponding
-- to the 4 possible memory location.

-- In Syrup we would have used a cable [<Bit>,<Bit>] but here we do
-- not want to bother with such low-level details as bit patterns.

data ADDR : Set where
  `0 : ADDR
  `1 : ADDR
  `2 : ADDR
  `3 : ADDR

-- We can write lookup (_!!_), the function which goes into the memory
-- configuration and grabs the value at the indicated location.
-- We do so by spelling out all the possible cases.

_!!_ : Vec ℕ 4 → ADDR → ℕ
(v ∷ _ ∷ _ ∷ _ ∷ []) !! `0 = v
(_ ∷ v ∷ _ ∷ _ ∷ []) !! `1 = v
(_ ∷ _ ∷ v ∷ _ ∷ []) !! `2 = v
(_ ∷ _ ∷ _ ∷ v ∷ []) !! `3 = v

-- In Agda we can run this function and prove that looking up the
-- content of mem (defined above) at address 1 returns 1. We do so
-- by stating an equality and writing a program that proves it holds.

_ : mem !! `1 ≡ 1
_ = trivial

-- NB: trivial is the proof that two things are equal so evidently
-- that the machine itself can see that it is true. Sometimes things
-- are not trivial and you actually need to do some work to convince
-- the machine.

-- Similarly we can write update (_[_]:=_), the function which goes
-- into the memory configuration and overwrites the content of the
-- indicated location with the indicated value.

_[_]:=_ : Vec ℕ 4 → ADDR → ℕ → Vec ℕ 4
(a ∷ b ∷ c ∷ d ∷ []) [ `0 ]:= v = v ∷ b ∷ c ∷ d ∷ []
(a ∷ b ∷ c ∷ d ∷ []) [ `1 ]:= v = a ∷ v ∷ c ∷ d ∷ []
(a ∷ b ∷ c ∷ d ∷ []) [ `2 ]:= v = a ∷ b ∷ v ∷ d ∷ []
(a ∷ b ∷ c ∷ d ∷ []) [ `3 ]:= v = a ∷ b ∷ c ∷ v ∷ []

-- We can once more run this function an verify that overriding the
-- content of mem at location 2 with 5 yields the memory configuration
-- 0 ∷ 1 ∷ 5 ∷ 3 ∷ []

_ : mem [ `2 ]:= 5 ≡ 0 ∷ 1 ∷ 5 ∷ 3 ∷ []
_ = trivial


----------------------------------------------------------------
-- The INSTRuction set of an ITSY machine
----------------------------------------------------------------

-- We only have 4 operations; we can:
-- LOAD  a value from a memory location as the new AC
-- STORE the value of the AC to a memory location
-- ADD   the content of a memory location to the AC
-- PRINT the value of the AC

data INSTR : Set where
  LOAD  : ADDR → INSTR
  STORE : ADDR → INSTR
  ADD   : ADDR → INSTR
  PRINT : INSTR

-- A program written in ITSY assembly (ASM) is a list of instructions.

ASM : Set
ASM = List INSTR

-- We can for instance write the program summing the content of
-- the memory and printing the result.

sum-MEM : ASM
sum-MEM
  = LOAD `0  -- AC becomes mem !! 0
  ∷ ADD `1   -- AC becomes mem !! 0 + mem !! 1
  ∷ ADD `2   -- AC becomes mem !! 0 + mem !! 1 + mem !! 2
  ∷ ADD `3   -- AC becomes mem !! 0 + mem !! 1 + mem !! 2 + mem !! 3
  ∷ PRINT    -- print result
  ∷ []

-- Or write the program swapping the values currently stored in
-- memory locations 0 and 3.

swap-03 : ASM
swap-03
  = LOAD `0   -- save value mem !! 0 in location 1
  ∷ STORE `1
  ∷ LOAD `3   -- put value mem !! 3 in location 0
  ∷ STORE `0
  ∷ LOAD `1   -- recover mem !! 0 in location 1 and put it in location 3
  ∷ STORE `3
  ∷ []

----------------------------------------------------------------
-- Giving a semantics (aka meaning) to ASM
----------------------------------------------------------------

-- It's all well and good to be able to define program but what do
-- they mean? Well, we can explain what each instruction mean by
-- describing its ACTION. Re-using a notion from "high-level concepts":
-- we are going to write an *interpreter* for ASM.

-- An ACTION takes a starting configuration as an input an returns
-- two things:
-- * the final configuration after executing the instruction
-- * the (potentially empty) list of natural numbers that
--   have been printed to the output queue

ACTION : Set
ACTION = ITSY → (ITSY × List ℕ)

-- Looking at each INSTR in isolation, we can translate its meaning
-- as an ACTION. I have interleaved the definition with comments to
-- clarify what each equation is saying.

instr : INSTR → ACTION

-- LOAD loads the new ac from the memory at the given location,
-- the memory is left unchanged and there are no outputs
instr (LOAD a)  (ac < mem >) = mem !! a        < mem            > , []

-- STORE stores the current ac in the memory at the given location,
-- the accumulator is not modified and there are no ouputs.
instr (STORE a) (ac < mem >) = ac              < mem [ a ]:= ac > , []

-- ADD adds the content of the memory at the given location to the
-- accumulator, the content of the memory is not changed and there are
-- no outputs.
instr (ADD a)   (ac < mem >) = ac + (mem !! a) < mem            > , []

-- PRINT puts the content of the accumulator in the input queue,
-- nothing else is modified.
instr PRINT     (ac < mem >) = ac              < mem            > , ac ∷ []


-- Just like we did for lookup and update, we can run this function
-- on individual instruction and prove what their behaviour is.
-- All the proofs are trivial.

_ : instr PRINT itsy ≡ (itsy , 0 ∷ [])
_ = trivial

_ : instr (LOAD `2) itsy ≡ (2 < mem > , [])
_ = trivial


-- Once we know how to run one instruction, running a list of instruction
-- is fairly straightforward (if a bit verbose).

asm : ASM → ACTION -- ASM = List INSTR

-- If the list of instructions is empty, we are done.
asm []       itsy = (itsy , [])

-- Otherwise we have an instruction i and a list of instruction is.
-- We start by running the instruction on the initial ITSY configuration
-- using instr. We get back a new configuration and some outputs.
-- We then run the rest of the instruction on this new configuration and
-- obtain a final configuration together with some more outputs.
-- We return the final configuration and append (++) the two lists of
-- outputs.
asm (i ∷ is) itsy =
  let (itsy₁ , ns₁) = instr i itsy
      (itsy₂ , ns₂) = asm is itsy₁
  in (itsy₂ , ns₁ ++ ns₂)

-- We can once more use our so-defined functions to run actual programs.
-- Here we swap the content of the memory at location 0 and 3 (overwriting
-- the content of the location 1 in the process) by runing swap-03 thanks
-- to asm.

_ : asm swap-03 itsy
  ≡ (0 < 3 ∷ 0 ∷ 2 ∷ 0 ∷ [] > , [])
_ = trivial

-- And here we sum the content of the memory and obtain 0+1+2+3, that
-- is to say 6.

_ : asm sum-MEM itsy ≡ (6 < mem > , 6 ∷ [])
_ = trivial

----------------------------------------------------------------
-- Proving programs correct
----------------------------------------------------------------

-- We have run our programs on some examples. This gives us some
-- sense that we have not messed up. However a successful test
-- does not mean we have not made any mistake. That is where we
-- need a proof.

-- The following type states that:
-- for all values (∀) ac and mem, the result of running sum-MEM
-- on the machine ac < mem > is actually the sum of the content
-- of the different memory locations.

-- Here we are not feeding concrete values: we are using abstract
-- one and our computer is symbolically executing sum-MEM and
-- figuring out that our claim is indeed correct! We have proven
-- our program correct: sum-MEM does indeed compute the sum!

theorem-sum-MEM : ∀ ac mem →
  let sum = mem !! `0 + mem !! `1 + mem !! `2 + mem !! `3 in
  asm sum-MEM (ac < mem >) ≡ (sum < mem > , sum ∷ [])
theorem-sum-MEM ac (a ∷ b ∷ c ∷ d ∷ []) = trivial

-- Similarly we can prove that for all values (∀) ac and mem,
-- there exists (∃) another value mem₂ such that running the
-- program swap-03 on ac < mem > produces a configuration where
-- the final state the memory is in is mem₂.
-- But more importanly, we also demand that:
-- * the content of mem at location 0 is the same as the content of mem₂ at location 3
-- * the content of mem at location 3 is the same as the content of mem₃ at location 0

-- That is to say, we have proven that swap-03 indeed swaps the
-- content of the memory at locations 0 and 3.

theorem-swap03 : ∀ ac mem → ∃ λ mem₂ →
    asm swap-03 (ac < mem >) ≡ ((mem !! `0) < mem₂ > , [])
  × mem₂ !! `0 ≡ mem !! `3
  × mem₂ !! `3 ≡ mem !! `0
theorem-swap03 ac (a ∷ b ∷ c ∷ d ∷ []) =
  _ , trivial , trivial , trivial

----------------------------------------------------------------
-- Proving programs equivalent
----------------------------------------------------------------

-- We like having correct programs. We also like having fast programs.
-- This means that if we are able to prove that we can apply some
-- optimisations making a program faster without changing its meaning
-- then we are going to be really happy.

-- Here we introduce a notion of behavioural equivalence between programs.
-- Two programs are behaviourally equivalent if they behave the same no
-- matter what the starting point is.
-- In other words, for all possible (∀) initial configuration itsy, running
-- is on itsy is equal to runing js on itsy.

_≅_ : ASM → ASM → Set
is ≅ js = ∀ itsy → asm is itsy ≡ asm js itsy

-- The first thing we can do is prove that performing two LOADs in a row
-- is a bit silly: only the effect of the second one will be seen. We can
-- therefore safely optimise away all double LOADs into single ones.
-- This proof is trivial.

theorem-loadload : ∀ l₁ l₂ →
  (LOAD l₁ ∷ LOAD l₂ ∷ []) ≅ (LOAD l₂ ∷ [])
theorem-loadload l₁ l₂ (ac < a ∷ b ∷ c ∷ d ∷ [] >) = trivial

-- Similarly storing the current accumulator to a location l and
-- then loading the value stored at location l is equivalent to
-- simply doing the STORE. Indeed, the value we are loading is
-- precisely the one we just put in which is to say the AC.

-- This proof is slightly less trivial: we need to consider all
-- the possible locations at hand. But once we have a concrete
-- location, it's trivial again. Hence this definition distinguishing
-- all possible values l may take.

theorem-storeload : ∀ l → (STORE l ∷ LOAD l ∷ []) ≅ (STORE l ∷ [])
theorem-storeload `0 (ac < a ∷ b ∷ c ∷ d ∷ [] >) = trivial
theorem-storeload `1 (ac < a ∷ b ∷ c ∷ d ∷ [] >) = trivial
theorem-storeload `2 (ac < a ∷ b ∷ c ∷ d ∷ [] >) = trivial
theorem-storeload `3 (ac < a ∷ b ∷ c ∷ d ∷ [] >) = trivial

-- I don't expect you to understand this last part. It is mostly here
-- to show you that we can have really complex proofs. But you should
-- be able to get an intuition for `theorem-cong`: it states that if
-- two programs (js and ks) behave the same then we can use either one
-- or the other *anywhere* in the middle of a longer program (here we
-- have some instructions is followed by either js or ks and then followed
-- by more instructions ls) and obtain two distinct programs that behave
-- the same.

-- This is a very powerful principle! It means that we can prove simple
-- optimisation principles like theorem-loadload and theorem-storeload
-- in isolation and then apply these optimisations anywhere we want in
-- arbitrarily more complex programs!

open import Data.List.Properties using (++-assoc)

theorem-append : ∀ is js itsy →
  asm (is ++ js) itsy ≡ (let (itsy₁ , ns₁) = asm is itsy
                             (itsy₂ , ns₂) = asm js itsy₁
                         in (itsy₂ , ns₁ ++ ns₂))
theorem-append []       js itsy = trivial
theorem-append (i ∷ is) js itsy
  with (itsyi   , ni)   ← instr i itsy         | λeq   ← theorem-append is js
  with (itsyis  , nis)  ← asm is itsyi         | eqis  ← λeq itsyi
  with (itsyjs  , njs)  ← asm js itsyis        | eqjs  ← eqis
  with (itsyijs , nijs) ← asm (is ++ js) itsyi | eqijs ← eqjs
  rewrite ++-assoc ni nis njs
  with eqijs
... | trivial = trivial

theorem-cong : ∀ is js ks ls →
  js ≅ ks → (is ++ js ++ ls) ≅ (is ++ ks ++ ls)
theorem-cong is js ks ls equiv itsy
  with asm is itsy
     | {asm (is ++ js ++ ls) itsy}
     | {asm (is ++ ks ++ ls) itsy}
     | {asm (js ++ ls) (proj₁ (asm is itsy))}
     | {asm (ks ++ ls) (proj₁ (asm is itsy))}
     | theorem-append is (js ++ ls) itsy
     | theorem-append is (ks ++ ls) itsy
     | theorem-append js ls (proj₁ (asm is itsy))
     | theorem-append ks ls (proj₁ (asm is itsy))
... | (itsyis , _) | trivial | trivial | trivial | trivial
  rewrite equiv itsyis = trivial

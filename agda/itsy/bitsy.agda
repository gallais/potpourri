module bitsy where

open import Data.Bool.Base using (T)
open import Data.Nat.Base  using (ℕ; _<ᵇ_; _+_)        -- Natural numbers: 0,1,2, ...
open import Data.List.Base using (List; []; _∷_; _++_) -- Finite lists, we only use lists of natural numbers here
open import Data.Product.Base using (_×_; _,_)
open import Data.Vec.Recursive hiding ([])             -- Vectors aka lists of a specific length
pattern [_] x = x
open import Data.Product   using (_×_ ; _,_; ∃; proj₁)  -- Pairs of values of different types
open import Relation.Binary.PropositionalEquality as Eq -- A notion of equality
  using (_≡_; sym; cong; cong₂) renaming (refl to tested)

open import Data.Unit.Base using (tt)
open import Agda.Builtin.FromNat
import Data.Nat.Literals
instance natLit = Data.Nat.Literals.number


----------------------------------------------------------------
-- An ITSY machine
----------------------------------------------------------------

-- We introduce an extremely simplified version of the TINY machine.
-- It has no flag register, no loop index, no input queue, and way
-- fewer instructions in its assembly language.

-- In our idealised setting we also do not worry about actually
-- storing the code into memory and having an instruction pointer.


----------------------------------------------------------------
-- Some basic digital logic
----------------------------------------------------------------

open import Data.Bool.Base as Bit using (if_then_else_)
  renaming ( Bool to Bit; true to I; false to O
           ; not to !_; _∨_ to _∣_; _∧_ to _&_)

<_> : Set → Set
< x > = x

mux : ∀ {a : Set} → (< Bit > × a × a) → a -- cheating!
mux (O , x , y) = x
mux (I , x , y) = y

xor : (< Bit > × < Bit >) → < Bit >
xor (x , y) = mux (x , y , ! y)

eq : (< Bit > × < Bit >) → < Bit >
eq (x , y) = ! xor (x , y)

split : ∀ {a : Set} n → < a ^ (n + n) > → < a ^ n > × < a ^ n > -- cheating!
split n = splitAt n n

merge : ∀ {a : Set} n → < a ^ n > × < a ^ n > → < a ^ (n + n) > -- cheating!
merge n (xs , ys) = append n n xs ys

merge4-split4 : (xs : < Bit ^ 4 >) →
                merge 2 (split 2 xs) ≡ xs
merge4-split4 ([ _ , _ , _ , _ ]) = tested

----------------------------------------------------------------
-- Some basic arithmetic
----------------------------------------------------------------

hadd : < Bit > × < Bit > → < Bit > × < Bit >
hadd (x1 , y1) = x1 & y1 , xor (x1 , y1)

fadd : < Bit > × < Bit > × < Bit > → < Bit > × < Bit >
fadd (x1 , y1 , c1)
  = let (a2 , a1) = hadd (x1 , y1) in
    let (b2 , r1) = hadd (c1 , a1) in
    a2 ∣ b2 , r1

----------------------------------------------------------------
-- A type of Words
----------------------------------------------------------------

pattern A = [ I , O , I , O ]
pattern B = [ I , O , I , I ]
pattern C = [ I , I , O , O ]
pattern D = [ I , I , O , I ]
pattern E = [ I , I , I , O ]
pattern F = [ I , I , I , I ]

fromℕ<16 : (n : ℕ) → {{T (n <ᵇ 16)}} → < Bit ^ 4 >
fromℕ<16 0  = [ O , O , O , O ]
fromℕ<16 1  = [ O , O , O , I ]
fromℕ<16 2  = [ O , O , I , O ]
fromℕ<16 3  = [ O , O , I , I ]
fromℕ<16 4  = [ O , I , O , O ]
fromℕ<16 5  = [ O , I , O , I ]
fromℕ<16 6  = [ O , I , I , O ]
fromℕ<16 7  = [ O , I , I , I ]
fromℕ<16 8  = [ I , O , O , O ]
fromℕ<16 9  = [ I , O , O , I ]
fromℕ<16 10 = A
fromℕ<16 11 = B
fromℕ<16 12 = C
fromℕ<16 13 = D
fromℕ<16 14 = E
fromℕ<16 15 = F

is0 : < Bit ^ 4 > → < Bit >
is0 [ O , O , O , O ] = I
is0 _ = O

number : Number < Bit ^ 4 >
Number.Constraint number = λ n → T (n <ᵇ 16)
Number.fromNat number = fromℕ<16

instance bit4Lit = number

rca2 : < Bit ^ 2 > × < Bit ^ 2 > × < Bit >
     → < Bit > × < Bit ^ 2 >
rca2 ([ x2 , x1 ] , [ y2 , y1 ] , c1)
  = let (c2 , z1) = fadd (x1 , y1 , c1) in
    let (c4 , z2) = fadd (x2 , y2 , c2) in
    (c4 , [ z2 , z1 ])


adc : < Bit ^ 4 > × < Bit ^ 4 > × < Bit >
    → < Bit     > -- overflow flag
    × < Bit     > -- carry flag
    × < Bit ^ 4 > -- result
adc (xs , ys , c1)
  = let (x84 , x21) = split 2 xs in
    let (y84 , y21) = split 2 ys in
    let (x8 , _)    = split 1 x84 in
    let (y8 , _)    = split 1 y84 in
    let (c4  , z21) = rca2 (x21 , y21 , c1) in
    let (c16 , z84) = rca2 (x84 , y84 , c4) in
    let (z8 , _)    = split 1 z84 in
    eq (x8 , y8) & xor (x8 , z8) , c16 , merge 2 (z84 , z21)

lift4 : ((< Bit > × < Bit >) → < Bit >)
      → ((< Bit ^ 4 > × < Bit ^ 4 >) → < Bit ^ 4 >)
lift4 f ([ x8 , x4 , x2 , x1 ] , [ y8 , y4 , y2 , y1 ])
  = [ f (x8 , y8) , f (x4 , y4) , f (x2 , y2) , f (x1 , y1) ]


xor4 = lift4 xor
or4  = lift4 (λ (x , y) → x ∣ y)
and4 = lift4 (λ (x , y) → x & y)
eq4  = lift4 eq

----------------------------------------------------------------
-- The state of an BITSY machine
----------------------------------------------------------------

-- We model the state of the BITSY machine as a record (i.e. a
-- collection of different values labelled by a name) containing:
--
-- * AC   the value of its accumulator
-- * MEM  the value contained in the 16 locations of its memory
-- * FR   the flag register

-- All of these values are < Bit ^ 4 >.

MEM : Set
MEM = < Bit ^ 4 > ^ 16

record BITSY : Set where
  constructor mkBITSY
  field FR    : < Bit ^ 4 >
        AC    : < Bit ^ 4 >
        CELLS : < MEM >
open BITSY

-- We can give some examples of memory and BITSY configurations

mem : < Bit ^ 4 > ^ 16
mem = [ 0 , 1 , 2 , 3 , 4 , 5 , 6 , 7 , 8 , 9 , A , B , C , D , E , F ]

itsy : BITSY
itsy = mkBITSY 0 0 mem

-- NB: the constructor mkBITSY was declared in the definition of BITSY,
-- it takes a value for the flag register, one for the accumulator and
-- a memory configuration and builds an BITSY machine configuration.

-- To refer to memory locations, we need a notion of addresses.
-- We have 16 memory locations and so ADDR is just 4 bits

ADDR : Set
ADDR = < Bit ^ 4 >

-- We can write lookup (_!!_), the function which goes into the memory
-- configuration and grabs the value at the indicated location.
-- We do so by spelling out all the possible cases.


_!!_ : MEM → ADDR → < Bit ^ 4 >
mem16 !! [ a8 , a4 , a2 , a1 ]
  = let (m07 , m8F) = split 8 mem16 in
    let mem8 = mux (a8 , m07 , m8F) in
    let (mem8l , mem8h) = split 4 mem8 in
    let mem4 = mux (a4 , mem8l , mem8h) in
    let (mem4l , mem4h) = split 2 mem4 in
    let mem2 = mux (a2 , mem4l , mem4h) in
    let (mem2l , mem2h) = split 1 mem2 in
    mux (a1 , mem2l , mem2h)

-- In Agda we can run this function and prove that looking up the
-- content of mem (defined above) at address 1 returns 1. We do so
-- by stating an equality and writing a program that proves it holds.

_ : mem !! A ≡ A
_ = tested

-- NB: just like in ask, tested is the proof that two things are equal
-- so evidently that the machine itself can see that it is true.
-- Sometimes things are not trivial and you actually need to do some
-- work to convince the machine.

-- Similarly we can write update (_[_]:=_), the function which goes
-- into the memory configuration and overwrites the content of the
-- indicated location with the indicated value.

_[_]:=_ : MEM → ADDR → < Bit ^ 4 > → MEM
mem16 [ a8 , a4 , a2 , a1 ]:= v
  = let (m07 , m8F) = split 8 mem16 in
    let mem8 = mux (a8 , m07 , m8F) in
    let (mem8l , mem8h) = split 4 mem8 in
    let mem4 = mux (a4 , mem8l , mem8h) in
    let (mem4l , mem4h) = split 2 mem4 in
    let mem2 = mux (a2 , mem4l , mem4h) in
    let (mem2l , mem2h) = split 1 mem2 in
    let mem1 = mux (a1 , mem2l , mem2h) in
    let upd1 = v in
    let upd2 = merge 1 (mux (a1 , upd1 , mem2l) , mux (a1 , mem2h , upd1)) in
    let upd4 = merge 2 (mux (a2 , upd2 , mem4l) , mux (a2 , mem4h , upd2)) in
    let upd8 = merge 4 (mux (a4 , upd4 , mem8l) , mux (a4 , mem8h , upd4)) in
    merge 8 (mux (a8 , upd8 , m07) , mux (a8 , m8F , upd8))

-- We can once more run this function an verify that overriding the
-- content of mem at location A with 0 yields the appropriate memory
-- configuration

_ : mem [ A ]:= 0
  ≡ [ 0 , 1 , 2 , 3 , 4 , 5 , 6 , 7 , 8 , 9 , 0 , B , C , D , E , F ]
_ = tested

----------------------------------------------------------------
-- The INSTRuction set of an BITSY machine
----------------------------------------------------------------

-- We only have 4 operations; we can:
-- LOAD  a value from a memory location as the new AC
-- STORE the value of the AC to a memory location
-- ADD   the content of a memory location to the AC
-- PRINT the value of the AC

data INSTR : Set where
  LDA : ADDR → INSTR
  STA : ADDR → INSTR
  ADC : ADDR → INSTR
  XOR : ADDR → INSTR
  PUT : INSTR
  HLT : INSTR

-- A program written in BITSY assembly (ASM) is a list of instructions.

ASM : Set
ASM = List INSTR

-- Or write the program swapping the values currently stored in
-- memory locations 0 and 3.

swap : ADDR → ADDR → ASM
swap l1 l2
  = LDA l1
  ∷ XOR l2    --
  ∷ STA l1    -- put value [ l1 ] xor [ l2 ] in location l1
  ∷ XOR l2    -- AC becomes ([ l1 ] xor [ l2 ]) xor [ l2 ] ≡ [ l1 ]
  ∷ STA l2
  ∷ XOR l1    -- AC becomes [ l1 ] xor ([ l1 ] xor [ l2 ]) ≡ [ l2 ]
  ∷ STA l1
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
ACTION = BITSY → (BITSY × List < Bit ^ 4 >)

-- Looking at each INSTR in isolation, we can translate its meaning
-- as an ACTION. I have interleaved the definition with comments to
-- clarify what each equation is saying.

instr : INSTR → ACTION

-- LOAD loads the new ac from the memory at the given location,
-- the memory is left unchanged and there are no outputs
instr (LDA l) (mkBITSY ([ hf , of , zf , cf ]) ac mem)
  = let ac′ = mem !! l in
    mkBITSY [ hf , of , is0 ac′ , cf ] ac′ mem , []

-- STORE stores the current ac in the memory at the given location,
-- the accumulator is not modified and there are no ouputs.
instr (STA l) (mkBITSY fr ac mem)
  = mkBITSY fr ac (mem [ l ]:= ac) , []

-- ADD adds the content of the memory at the given location to the
-- accumulator, the content of the memory is not changed and there are
-- no outputs.
instr (ADC l) (mkBITSY ([ hf , _ , zf , cf ]) ac mem)
  = let (of , co , sum) = adc (ac , mem !! l , cf) in
    mkBITSY ([ hf , of , is0 sum , co ]) sum mem , []

instr (XOR l) (mkBITSY fr ac mem)
  = mkBITSY fr (xor4 (ac , mem !! l)) mem , []

-- PRINT puts the content of the accumulator in the input queue,
-- nothing else is modified.
instr (PUT  ) (mkBITSY fr ac mem) = mkBITSY fr ac mem , ac ∷ []

instr (HLT  ) (mkBITSY [ _ , ov , zf , cf ] ac mem)
  = (mkBITSY [ I , ov , zf , cf ] ac mem , [])

-- Just like we did for lookup and update, we can run this function
-- on individual instruction and prove what their behaviour is.
-- All the proofs are trivial.

_ : instr PUT itsy ≡ (itsy , 0 ∷ [])
_ = tested

_ : instr (LDA 2) itsy ≡ (mkBITSY 0 2 mem , [])
_ = tested

-- Once we know how to run one instruction, running a list of instruction
-- is fairly straightforward (if a bit verbose).

asm : ASM → ACTION -- ASM = List INSTR

-- If the list of instructions is empty, we are done.
asm [] itsy = itsy , []

-- Otherwise we have an instruction i and a list of instruction is.
-- We start by running the instruction on the initial BITSY configuration
-- using instr. We get back a new configuration and some outputs.
-- We then run the rest of the instruction on this new configuration and
-- obtain a final configuration together with some more outputs.
-- We return the final configuration and append (++) the two lists of
-- outputs.
asm (i ∷ is) itsy =
  let (itsy₁@(mkBITSY [ hf , _ , _ , _ ] _ _) , ns₁) = instr i itsy in
  if hf then itsy₁ , ns₁ else
  let (itsy₂ , ns₂) = asm is itsy₁
  in (itsy₂ , ns₁ ++ ns₂)

-- We can once more use our so-defined functions to run actual programs.
-- Here we swap the content of the memory at location 0 and 3 (overwriting
-- the content of the location 1 in the process) by runing swap-03 thanks
-- to asm.

_ : asm (swap 1 3) itsy
  ≡ (mkBITSY 0 3 [ 0 , 3 , 2 , 1 , 4 , 5 , 6 , 7 , 8 , 9 , A , B , C , D , E , F ]
  , [])
_ = tested

open import Data.Bool.Properties using (not-involutive)

xor-comm : ∀ x y → xor(x , y) ≡ xor(y , x)
xor-comm O O = tested
xor-comm O I = tested
xor-comm I O = tested
xor-comm I I = tested

xor-assoc : ∀ x y z → xor(xor(x , y), z) ≡ xor(x , xor(y , z))
xor-assoc O y z = tested
xor-assoc I O z = tested
xor-assoc I I z = sym (not-involutive z)

xor-diag : ∀ x → xor(x , x) ≡ O
xor-diag O = tested
xor-diag I = tested

xor-identityˡ : ∀ x → xor(O , x) ≡ x
xor-identityˡ O = tested
xor-identityˡ I = tested

xor-identityʳ : ∀ x → xor(x , O) ≡ x
xor-identityʳ O = tested
xor-identityʳ I = tested

lift4-comm :
  ∀ f → (∀ x y → f(x , y) ≡ f(y , x)) →
  ∀ xs ys → lift4 f (xs , ys) ≡ lift4 f (ys , xs)
lift4-comm f f-comm [ x8 , x4 , x2 , x1 ] [ y8 , y4 , y2 , y1 ]
  rewrite f-comm x8 y8 | f-comm x4 y4 | f-comm x2 y2 | f-comm x1 y1
  = tested

lift4-assoc :
  ∀ f → (∀ x y z → f(f(x , y), z) ≡ f(x , f(y , z))) →
  ∀ xs ys zs → lift4 f (lift4 f (xs , ys), zs) ≡ lift4 f (xs , lift4 f (ys , zs))
lift4-assoc f f-assoc
  [ x8 , x4 , x2 , x1 ] [ y8 , y4 , y2 , y1 ] [ z8 , z4 , z2 , z1 ]
  rewrite f-assoc x8 y8 z8 | f-assoc x4 y4 z4 | f-assoc x2 y2 z2 | f-assoc x1 y1 z1
  = tested

lift4-diag :
  ∀ f v → (∀ x → f(x , x) ≡ v) →
  ∀ xs → lift4 f (xs , xs) ≡ [ v , v , v , v ]
lift4-diag f v f-diag [ x8 , x4 , x2 , x1 ]
  rewrite f-diag x8 | f-diag x4 | f-diag x2 | f-diag x1
  = tested

lift4-identityˡ :
  ∀ f v → (∀ x → f(v , x) ≡ x) →
  ∀ xs → lift4 f ([ v , v , v , v ] , xs) ≡ xs
lift4-identityˡ f v f-identityˡ [ x8 , x4 , x2 , x1 ]
  rewrite f-identityˡ x8 | f-identityˡ x4 | f-identityˡ x2 | f-identityˡ x1
  = tested

lift4-identityʳ :
  ∀ f v → (∀ x → f(x , v) ≡ x) →
  ∀ xs → lift4 f (xs , [ v , v , v , v ]) ≡ xs
lift4-identityʳ f v f-identityʳ [ x8 , x4 , x2 , x1 ]
  rewrite f-identityʳ x8 | f-identityʳ x4 | f-identityʳ x2 | f-identityʳ x1
  = tested

swap-correct : ∀ a b {of zf cf ac rest} →
  let (mkBITSY _ _ final , _) = asm (swap 0 1) (mkBITSY [ O , of , zf , cf ] ac (a , b , rest)) in
  final ≡ (b , a , rest)
swap-correct a b {rest = rest}

  = cong₂ (λ a b → a , b , rest) l1-correct l2-correct where

  open Eq.≡-Reasoning

  l2-correct : _
  l2-correct = begin
    xor4(xor4(a , b) , b)
      ≡⟨ lift4-assoc xor xor-assoc a b b ⟩
    xor4(a , xor4(b , b))
      ≡⟨ cong (λ y → xor4(a , y)) (lift4-diag xor O xor-diag b) ⟩
    xor4(a , 0)
      ≡⟨ lift4-identityʳ xor O xor-identityʳ a ⟩
    a
   ∎

  l1-correct : _
  l1-correct = begin
    xor4(xor4(xor4(a , b) , b) , xor4(a , b))
      ≡⟨ cong (λ y → xor4(y , xor4(a , b))) l2-correct ⟩
    xor4(a , xor4(a , b))
      ≡⟨ lift4-assoc xor xor-assoc a a b ⟨
    xor4(xor4(a , a) , b)
      ≡⟨ cong (λ y → xor4(y , b)) (lift4-diag xor O xor-diag a) ⟩
    xor4(0 , b)
      ≡⟨ lift4-identityˡ xor O xor-identityˡ b ⟩
    b ∎

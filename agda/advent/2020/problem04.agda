module problem04 where

open import Category.Applicative

open import Data.Bool.Base
open import Data.Bool.Properties using (T?)
open import Data.Char.Base using (Char)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.NonEmpty as List⁺ using (List⁺)
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just; maybe′)
import Data.Maybe.Categorical as Maybe
open import Data.Nat.Base
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_; proj₁; proj₂; uncurry)
open import Data.String.Base as String using (String)
open import Data.Sum.Base

open import Function.Base
open import Function.Identity.Categorical using (Identity)
open import Level using (0ℓ)
open import Level.Bounded using ([_])

open import Relation.Unary
open import Text.Parser 0ℓ as Combinators using (Parser; runParserIO)

data Unit : Set where CM IN : Unit

data EyeColor : Set where Amb Blu Brn Gry Grn Hzl Oth : EyeColor

record Passport' (F : Set → Set) : Set where
  constructor MkPassport
  field byr : F ℕ
        iyr : F ℕ
        eyr : F ℕ
        hgt : F (ℕ × Maybe Unit)
        hcl : F (List⁺ ℕ ⊎ List⁺ Char)
        ecl : F (EyeColor ⊎ List⁺ Char)
        pid : F (List⁺ ℕ ⊎ List⁺ Char)
        cid : Maybe ℕ

Passport = Passport' Identity

initPassport : Passport' Maybe
initPassport = record
                 { byr = nothing
                 ; iyr = nothing
                 ; eyr = nothing
                 ; hgt = nothing
                 ; hcl = nothing
                 ; ecl = nothing
                 ; pid = nothing
                 ; cid = nothing
                 }

passports : ∀[ Parser [ List⁺ (Passport' Maybe) ] ]
passports = list⁺ (passport <&? box spaces) where

  open Combinators

  mkPassport : List⁺ (Passport' Maybe → Passport' Maybe) → Passport' Maybe
  mkPassport = List⁺.foldr _$_ (_$ initPassport)

  trash : ∀[ Parser [ List⁺ Char ] ]
  trash = list⁺ (noneOf ( ' ' ∷ '\t' ∷ '\n' ∷ [])) <& box space

  hgt : ∀[ Parser [ (Passport' Maybe → Passport' Maybe) ] ]
  hgt = update <$> (text "hgt:" &> box decimalℕ <&?> box unit <& box space)

    where
      unit : ∀[ Parser [ Unit ] ]
      unit = (CM <$ text "cm") <|> (IN <$ text "in")

      update : ℕ × Maybe Unit → Passport' Maybe → Passport' Maybe
      update res m = record m { hgt = just res }

  hcl : ∀[ Parser [ (Passport' Maybe → Passport' Maybe) ] ]
  hcl = update <$> (text "hcl:"
                &> box ((char '#' &> box (list⁺ hexadecimalDigit <& box space)) <⊎> trash))

    where

      update : List⁺ ℕ ⊎ List⁺ Char → Passport' Maybe → Passport' Maybe
      update res m = record m { hcl = just res }

  ecl : ∀[ Parser [ (Passport' Maybe → Passport' Maybe) ] ]
  ecl = update <$> (text "ecl:" &> box ((eyeColor <& box space) <⊎> trash))

   where

      eyeColor : ∀[ Parser [ EyeColor ] ]
      eyeColor = alts $ (Amb <$ text "amb")
                      ∷ (Blu <$ text "blu")
                      ∷ (Brn <$ text "brn")
                      ∷ (Gry <$ text "gry")
                      ∷ (Grn <$ text "grn")
                      ∷ (Hzl <$ text "hzl")
                      ∷ (Oth <$ text "oth")
                      ∷ []

      update : EyeColor ⊎ List⁺ Char → Passport' Maybe → Passport' Maybe
      update res m = record m { ecl = just res }

  pid : ∀[ Parser [ (Passport' Maybe → Passport' Maybe) ] ]
  pid = update <$> (text "pid:" &> box ((list⁺ decimalDigit <& box space) <⊎> trash))

   where

      update : List⁺ ℕ ⊎ List⁺ Char → Passport' Maybe → Passport' Maybe
      update res m = record m { pid = just res }


  fields : ∀ {n} → List (Parser [ (Passport' Maybe → Passport' Maybe) ] n)
  fields = (text "byr:" &> box ((λ n r → record r { byr = just n }) <$> decimalℕ) <& box space)
         ∷ (text "iyr:" &> box ((λ n r → record r { iyr = just n }) <$> decimalℕ) <& box space)
         ∷ (text "eyr:" &> box ((λ n r → record r { eyr = just n }) <$> decimalℕ) <& box space)
         ∷ hgt
         ∷ hcl
         ∷ ecl
         ∷ pid
         ∷ (text "cid:" &> box ((λ n r → record r { cid = just n }) <$> decimalℕ) <& box space)
         ∷ []

  passport : ∀[ Parser [ Passport' Maybe ] ]
  passport = mkPassport <$> list⁺ (alts fields)

validate : Passport' Maybe → Maybe Passport
validate (MkPassport byr iyr eyr hgt hcl ecl pid cid) =
  let open RawApplicative Maybe.applicative renaming (_⊛_ to _<*>_) in
  (_$ cid) <$> ⦇ MkPassport byr iyr eyr hgt hcl ecl pid ⦈


open import IO
open import System.Environment

getInput : IO String
getInput = do
  args ← getArgs
  (just fp) ← pure (List.head args)
    where _ → pure ""
  readFiniteFile fp

check : Passport → Bool
check p = let open Passport' p in List.and
  $ (1920 ≤ᵇ byr) ∷ (byr ≤ᵇ 2002)
  ∷ (2010 ≤ᵇ iyr) ∷ (iyr ≤ᵇ 2020)
  ∷ (2020 ≤ᵇ eyr) ∷ (eyr ≤ᵇ 2030)
  ∷ maybe′ (heightCheck (proj₁ hgt)) false (proj₂ hgt)
  ∷ [ (λ ds → List⁺.length ds ≡ᵇ 6) , const false ]′ hcl
  ∷ [ const true , const false ]′ ecl
  ∷ [ (λ ds → List⁺.length ds ≡ᵇ 9) , const false ]′ pid
  ∷ [] where

  heightCheck : ℕ → Unit → Bool
  heightCheck val CM = (150 ≤ᵇ val) ∧ (val ≤ᵇ 193)
  heightCheck val IN = (59 ≤ᵇ val) ∧ (val ≤ᵇ 76)

main = run $ do
  content ← getInput
  passports ← runParserIO passports content
  let valid₁ = List.mapMaybe validate (List⁺.toList passports)
  putStrLn $ show $ List.length valid₁
  let valid₂ = List.filter (T? ∘ check) valid₁
  putStrLn $ show $ List.length valid₂

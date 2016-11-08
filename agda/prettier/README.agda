module README where

-- The following content is based on Philip Wadler's
-- "A prettier printer."

open import Section1.Core
open import Section1.Examples

open import Section2.Core
open import Section2.Examples

open import Section3.Core

open import Section4.Core
open import Section4.Examples

-- The examples are based on the following Data definitions:

open import Data.Tree
open import Data.XML


-- Implementation details:

open import Utils
open import Size
open import Data.Nat
open import Data.Bool
open import Data.String.Extra

-- The implementation in Agda is fairly straightforward.
-- It however relies on 3 different tricks to help the
-- termination checker in 3 distinct places:

-- 1. Using a Vec rather than a List when the elements in
--    the list may be modified before the recursive call.
--    The length of the Vec gets smaller no matter what
--    happens to the elements in it. Cf:

_ : the-definition Section4.Core.pressImplementation.fill {0}
_ = _

-- 2. Instead of using a stack to store the subterms on
--    which to call the procedure recursively, carry around
--    a continuation. This way the termination checker sees
--    immediately that the recursive calls are justified. Cf:

_ : the-definition Section4.Core.pressImplementation.best {true}
_ = _

-- 3. Using sized types to make explicit the fact that all of
--    the children of a rosetree's node are subterms.
_ : the-definition Data.XML.XML
_ = _

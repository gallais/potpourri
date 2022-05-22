open import Level
open import Data.Container using (Container; ⟦_⟧)
open import Data.Product using (_,_)
open import Relation.Unary

open import Data.Container.Relation.Unary.All as □ using (□)
open import Data.Container.Relation.Unary.Any as ◇ using (◇)

module _ {C : Container 0ℓ 0ℓ} {X : Set}
         {P : Pred X 0ℓ} {Q : Set} {x} where

  dual : (◇ C P x → Q) →
         (□ C (λ x → P x → Q) x)
  dual f = □.all (λ pos px → f (◇.any (pos , px)))

  laud : (□ C (λ x → P x → Q) x) →
         (◇ C P x → Q)
  laud f (◇.any (pos , px)) = f .□.proof pos px

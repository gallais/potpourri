open import Level
open import Data.Container using (Container; ⟦_⟧)
open import Data.Product using (_,_)
open import Relation.Unary

open import Data.Container.Relation.Unary.All as □ using (□)
open import Data.Container.Relation.Unary.Any as ◇ using (◇)

module _ {C : Container 0ℓ 0ℓ} {X Y : Set}
         {P : Pred X 0ℓ} {Q : Pred Y 0ℓ} {x y} where

  dual : (◇ C P x → Q y) →
         (□ C (λ x → P x → Q y) x)
  dual f = □.all (λ pos px → f (◇.any (pos , px)))

  laud : (□ C (λ x → P x → Q y) x) →
         (◇ C P x → Q y)
  laud f (◇.any (pos , px)) = f .□.proof pos px

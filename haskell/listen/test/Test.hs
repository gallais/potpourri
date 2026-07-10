module Main (main) where

import Test.QuickCheck
import Test.Tasty (defaultMain, TestTree, testGroup)
import Test.Tasty.QuickCheck (testProperty)

import Problem
import qualified Solution
import qualified Okasaki

instance Arbitrary a => Arbitrary (Tree a) where
  arbitrary = sized tree where

    tree 0 = Leaf <$> arbitrary
    tree n | n > 0 = oneof
      [ Leaf <$> arbitrary
      , Node <$> subtree <*> subtree
      ] where subtree = tree (n `div` 2)

rebuild_prop :: Problem -> Tree Int -> Bool
rebuild_prop sol = \ t -> sol (breadthFirst t) == Just t


main :: IO ()
main = defaultMain $ testGroup "rebuild" $
  [ testProperty "Solution" (rebuild_prop Solution.rebuild)
  , testProperty "Okasaki" (rebuild_prop Okasaki.rebuild)
  ]

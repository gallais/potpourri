module Main (main) where

import Test.QuickCheck
import Test.Tasty (defaultMain, TestTree, testGroup)
import Test.Tasty.QuickCheck (testProperty)

import Problem
import Solution

instance Arbitrary a => Arbitrary (Tree a) where
  arbitrary = sized tree where

    tree 0 = Leaf <$> arbitrary
    tree n | n > 0 = oneof
      [ Leaf <$> arbitrary
      , Node <$> subtree <*> subtree
      ] where subtree = tree (n `div` 2)

main :: IO ()
main = defaultMain $ testProperty "rebuild" $ \ t ->
  rebuild (breadthFirst (t :: Tree Int)) == Just t

module Language.Clump.Syntax where

import Control.Applicative (Const)
import Control.Monad.Identity (Identity)
import Data.Text (Text)

data Reference
  = Relative Integer
  | Absolute Integer
  deriving (Show)

next :: Reference -> Reference
next ref = case ref of
  Relative i -> Relative (1 + i)
  Absolute{} -> ref

data Address ty = Address
  { nrow :: Reference
  , ncol :: Reference
  } deriving (Show)

data RawExpr where
  RawVal :: Text -> RawExpr
  RawRef :: Text -> RawExpr
  RawAdd :: RawExpr -> RawExpr -> RawExpr
  RawSum :: Text -> Text -> RawExpr
  deriving (Show)

data TypExpr ty where
  Val :: ty -> TypExpr ty
  Ref :: Address ty -> TypExpr ty
  Add :: TypExpr Integer -> TypExpr Integer -> TypExpr Integer
  Sum :: Address Integer -> Address Integer -> TypExpr Integer

deriving instance Show ty => Show (TypExpr ty)

data Chunk v
  = AString Text
  | AnExpr v
  deriving (Show)

newtype Doc v = Doc { getDoc :: [Block v] }
  deriving (Show)

data Block v
  = CSV Text [Row v]
  | CLP [Chunk v]
  deriving (Show)

newtype Row v = Row { getRow :: [v] }
  deriving (Show)

type RawCell = RawExpr
data TypCell = forall ty. Show ty => TypCell (TypExpr ty)
deriving instance Show TypCell

type Raw t = t RawExpr
type Typ t = t TypCell

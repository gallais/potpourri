module Language.Clump.Parser where

import Control.Applicative (Const(Const))
import Data.Char (isAlpha, isAlphaNum)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import Text.Parsec

import Language.Clump.Syntax

type Parser a = Parsec Text () a

identifier :: Parser Text
identifier = fmap Text.pack $
  (:) <$> satisfy isAlpha <*> many (satisfy isAlphaNum)

doc :: Parser (Raw Doc)
doc = Doc <$ spaces <*> many (id <$> block <* newline <* spaces) <* eof

block :: Parser (Raw Block)
block = choice
  [ CSV <$ string "DATA" <* spaces
      <*> identifier <* spaces
      <* char '{' <* spaces
      <*> many (id <$> row <* spaces)
      <* char '}'
  , CLP <$> many1 chunk
  ]

chunk :: Parser (Raw Chunk)
chunk = AString . Text.pack <$> many1 (noneOf "D\n")

row :: Parser (Raw Row)
row =
  Row <$> sepBy cell (char ',') <* char ';'
    <* spaces

address :: Parser Text
address = do
  col <- anyChar
  row <- anyChar
  pure $ Text.pack [col,row]


expr :: Parser RawExpr
expr =
  RawSum <$ string "sum" <* spaces
    <* char '(' <* spaces
    <*> address
    <* char ':'
    <*> address
    <* char ')'
  <|> id <$ char '(' <* spaces <*> expr <* spaces <* char ')'

cell :: Parser RawCell
cell =
  id <$ char '{' <* spaces <*> expr <* spaces <* char '}'
  <|>
  RawVal . Text.pack <$> many (noneOf ",;")


getDoc :: IO ()
getDoc = do
  clp <- Text.readFile "test/sample.clp"
  parseTest doc clp

module Data.SubSet where

newtype SubSet s t = SubSet { embed :: s -> t }

data DecidableSubSet s t =
  DecidableSubSet { subSet :: SubSet s t
                  , decide :: t -> Maybe s }

complement :: DecidableSubSet s t -> DecidableSubSet t t
complement dec = DecidableSubSet
  { subSet = SubSet id
  , decide = \ t -> maybe (Just t) (const Nothing) $ decide dec t }

module Data.Pixel where

import Data.Word
import Data.List
import Codec.Picture
import Control.Monad

class Averageable a where
  average :: [a] -> Maybe a

averageIntegral :: Integral a => [a] -> Maybe a
averageIntegral ns = do
  guard (len /= 0)
  return $ fromIntegral $ sum ns' `quot` len
  where ns' = fmap toInteger ns
        len = genericLength ns

averageRealFractional :: (Real a, Fractional a) => [a] -> Maybe a
averageRealFractional ns = do
  guard (len /= 0)
  return $ fromRational $ sum ns' / len
  where ns' = fmap toRational ns
        len = fromIntegral $ max 1 $ genericLength ns

instance Averageable Word8 where
  average = averageIntegral

instance Averageable Word16 where
  average = averageIntegral

instance Averageable Word32 where
  average = averageIntegral

instance Averageable Float where
  average = averageRealFractional

instance Averageable PixelYA8 where
  average ps =
    let (xs, ys) = unzip $ fmap (\ (PixelYA8 x y) -> (x,y)) ps in
    PixelYA8 <$> average xs <*> average ys

instance Averageable PixelYA16 where
  average ps =
    let (xs, ys) = unzip $ fmap (\ (PixelYA16 x y) -> (x,y)) ps in
    PixelYA16 <$> average xs <*> average ys

instance Averageable PixelRGB8 where
  average ps =
    let (xs, ys, zs) = unzip3 $ fmap (\ (PixelRGB8 x y z) -> (x,y,z)) ps in
    PixelRGB8 <$> average xs <*> average ys <*> average zs

instance Averageable PixelRGB16 where
  average ps =
    let (xs, ys, zs) = unzip3 $ fmap (\ (PixelRGB16 x y z) -> (x,y,z)) ps in
    PixelRGB16 <$> average xs <*> average ys <*> average zs

instance Averageable PixelRGBF where
  average ps =
    let (xs, ys, zs) = unzip3 $ fmap (\ (PixelRGBF x y z) -> (x,y,z)) ps in
    PixelRGBF <$> average xs <*> average ys <*> average zs

instance Averageable PixelYCbCr8 where
  average ps =
    let (xs, ys, zs) = unzip3 $ fmap (\ (PixelYCbCr8 x y z) -> (x,y,z)) ps in
    PixelYCbCr8 <$> average xs <*> average ys <*> average zs

instance Averageable PixelCMYK8 where
  average ps =
    let (xs, ys, zs, ts) = unzip4 $ fmap (\ (PixelCMYK8 x y z t) -> (x,y,z,t)) ps in
    PixelCMYK8 <$> average xs <*> average ys <*> average zs <*> average ts

instance Averageable PixelCMYK16 where
  average ps =
    let (xs, ys, zs, ts) = unzip4 $ fmap (\ (PixelCMYK16 x y z t) -> (x,y,z,t)) ps in
    PixelCMYK16 <$> average xs <*> average ys <*> average zs <*> average ts

instance Averageable PixelRGBA8 where
  average ps =
    let (xs, ys, zs, ts) = unzip4 $ fmap (\ (PixelRGBA8 x y z t) -> (x,y,z,t)) ps in
    PixelRGBA8 <$> average xs <*> average ys <*> average zs <*> average ts

instance Averageable PixelRGBA16 where
  average ps =
    let (xs, ys, zs, ts) = unzip4 $ fmap (\ (PixelRGBA16 x y z t) -> (x,y,z,t)) ps in
    PixelRGBA16 <$> average xs <*> average ys <*> average zs <*> average ts

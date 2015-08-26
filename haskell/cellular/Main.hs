module Main where

import Data.SubSet
import Data.Cellular
import Data.List
import Data.Monoid
import Data.Function.Memoize

import Codec.Picture

import System.Environment

import Control.Monad

instance Memoizable a => Memoizable (Sum a) where
  memoize f = memoize (f . Sum) . getSum

box :: (Num a, Ord a) => a -> a -> DecidableSubSet (a, a) (a, a)
box w h = DecidableSubSet { subSet = SubSet id,  decide = dec} where
  dec el@(x, y) = guard (0 <= x && x < w && 0 <= y && y < h) >> return el

growImageCellular :: (Num a, Ord b, Pixel b) => Cellular (a, a) b
growImageCellular = Cellular $ head . tail . top3 where
  top3 f     = take 3 $ sortBy (flip compare) $ f <$> neighbours
  neighbours = (,) <$> [-1,0,1] <*> [-1,0,1]

growImagePreCellular :: (Num a, Ord a, Ord b, Pixel b) => a -> a -> PreCellular (a, a) (a, a) b
growImagePreCellular w h = PreCellular
  { decidableSubSet = complement $ box w h
  , cellular        = growImageCellular }

black :: Pixel a => Image a -> a
black img = let px = pixelAt img 0 0 in mixWith (\ _ _ _ -> 0) px px

-- here we use newtype wrappers to tell Haskell which
-- monoid to pick.
growImage :: (Pixel a, Ord a) => Image a -> [(Int, Int) -> a]
growImage img = finish $ runP (growImagePreCellular width height) init
  where finish = fmap (\ f (x, y) -> f (Sum x, Sum y))
        width  = Sum $ imageWidth img
        height = Sum $ imageHeight img
        init   = either (const $ black img)
                        (\ (x, y) -> pixelAt img (getSum x) (getSum y))

extendedImage :: (Ord a, Pixel a) => Image a -> Int -> Image a
extendedImage img ext = generateImage newOne (width + 2 * ext) (height + 2 * ext)
  where width  = imageWidth img
        height = imageHeight img
        growth = growImage img !! ext
        newOne = \ x y -> maybe (growth (x - ext, y - ext)) (uncurry $ pixelAt img)
                                $ decide (box width height) (x - ext, y - ext)

extendedDynamicImage :: DynamicImage -> Int -> DynamicImage
extendedDynamicImage dimg ext = case dimg of
  ImageY8     img -> ImageY8     $ extendedImage img ext
  ImageY16    img -> ImageY16    $ extendedImage img ext
  ImageYF     img -> ImageYF     $ extendedImage img ext
  ImageYA8    img -> ImageYA8    $ extendedImage img ext
  ImageYA16   img -> ImageYA16   $ extendedImage img ext
  ImageRGB8   img -> ImageRGB8   $ extendedImage img ext
  ImageRGB16  img -> ImageRGB16  $ extendedImage img ext
  ImageRGBF   img -> ImageRGBF   $ extendedImage img ext
  ImageRGBA8  img -> ImageRGBA8  $ extendedImage img ext
  ImageRGBA16 img -> ImageRGBA16 $ extendedImage img ext
  ImageYCbCr8 img -> ImageYCbCr8 $ extendedImage img ext
  ImageCMYK8  img -> ImageCMYK8  $ extendedImage img ext
  ImageCMYK16 img -> ImageCMYK16 $ extendedImage img ext


main :: IO ()
main = do
  (fp : n : _) <- getArgs
  (Right img)  <- readImage $ fp
  savePngImage (fp ++ ".ext" ++ n ++ ".png") $ extendedDynamicImage img $ read n


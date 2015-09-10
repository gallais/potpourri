{-# LANGUAGE RankNTypes            #-}

module Main where

import Data.Bijection
import Data.DecidableSubset as DS

import Data.Cellular
import Data.Pixel

import Data.Function
import Data.Maybe
import Data.List
import Data.Monoid
import Data.Function.Memoize

import Codec.Picture

import System.Environment

import Control.Monad
import Control.Monad.Identity
import Control.Monad.Primitive
import System.Random

region :: (Num a, Ord a, Integral a) => a -> a -> a -> DecidableSubset (a, a) (Sum a, Sum a)
region w h s = castBox $ DS.intersection outerDS imageDS
  where box x w y h = DS.cartesian (DS.range x (x + w - 1)) (DS.range y (y + h - 1))
        outerDS     = DS.complement $ box 0 w 0 h
        imageDS     = box (-s) (w + 2 * s) (-s) (h + 2 * s)
        castBox b   = DS.bijection b identity (pair monoidSum monoidSum)

-- Various strategies:
mkCellular :: (Num a, Pixel b, Monad m) =>
              ([b] -> m (Maybe b)) -> CellularT m (a, a) (Maybe b)
mkCellular f = Cellular $ (f . catMaybes =<<) . sequence . (<$> neighbours)
  where neighbours = (,) <$> [-1,0,1] <*> [-1,0,1]

medianTop3 :: (Num a, Ord b, Pixel b, Monad m) => CellularT m (a, a) (Maybe b)
medianTop3 = mkCellular $ return . second . top3
 where second xs = guard (length xs >= 2) >> return (xs !! 2)
       top3      = take 3 . sortBy (flip compare)

averageAll :: (Num a, Averageable b, Ord b, Pixel b, Monad m) =>
              CellularT m (a, a) (Maybe b)
averageAll = mkCellular $ return . average

averageTopN :: (Num a, Averageable b, Ord b, Pixel b, Monad m) =>
               Integer -> CellularT m (a, a) (Maybe b)
averageTopN n = mkCellular $ return . average . topN n
  where topN n = genericTake n . sortBy (flip compare)

randomPick :: (Num a, Pixel b) => CellularT IO (a, a) (Maybe b)
randomPick = mkCellular select
  where select xs = (\ n -> guard (not $ null xs) >> return (xs !! n))
                    <$> randomRIO (0, length xs - 1)

black :: Pixel a => Image a -> a
black img = let px = pixelAt img 0 0 in mixWith (\ _ _ _ -> 0) px px

extendImage :: (Pixel a, Ord a, Monad m, PrimMonad m) =>
               Int -> CellularT m (Integer, Integer) (Maybe a) -> Image a -> m (Image a)
extendImage n cell img = makeImage (last . take (n + 1) $ runPM preCell init)
  where
    makeImage          = withImage (width + 2 * n) (height + 2 * n) . defaultBlack
    defaultBlack state = \ x y ->
      let x' = x - n; y' = y - n in
      maybe (return $ pixelAt img x' y')
            (fmap (maybe (black img) id) . state)
            $ decide regionDS (Sum (fromIntegral x'), Sum (fromIntegral y'))

    preCell            = PreCellular regionDS $ Cellular
                       $ \ init -> delta cell $ \ (x, y) -> init (Sum x, Sum y)

    init               = either (const $ return $ Nothing)
                                (uncurry ((\ x y -> return $ do
                                   guard (0 <= x && x < width)
                                   guard (0 <= y && y < height)
                                   return (pixelAt img  x y)) `on` (fromIntegral . getSum)))

    width              = imageWidth img
    height             = imageHeight img
    regionDS           = region (fromIntegral width) (fromIntegral height) (fromIntegral n)

mapMDynamicImage :: Monad m =>
 (forall a. (Pixel a, Ord a, Averageable a) => Image a -> m (Image a)) -> DynamicImage -> m DynamicImage
mapMDynamicImage f dimg = case dimg of
  ImageY8     img -> ImageY8     <$> f img
  ImageY16    img -> ImageY16    <$> f img
  ImageYF     img -> ImageYF     <$> f img
  ImageYA8    img -> ImageYA8    <$> f img
  ImageYA16   img -> ImageYA16   <$> f img
  ImageRGB8   img -> ImageRGB8   <$> f img
  ImageRGB16  img -> ImageRGB16  <$> f img
  ImageRGBF   img -> ImageRGBF   <$> f img
  ImageRGBA8  img -> ImageRGBA8  <$> f img
  ImageRGBA16 img -> ImageRGBA16 <$> f img
  ImageYCbCr8 img -> ImageYCbCr8 <$> f img
  ImageCMYK8  img -> ImageCMYK8  <$> f img
  ImageCMYK16 img -> ImageCMYK16 <$> f img

main :: IO ()
main = do
  (fp : n : _) <- getArgs
  (Right img)  <- readImage $ fp
  extendedImg  <- mapMDynamicImage (extendImage (read n) $ randomPick) img
  savePngImage (fp ++ ".ext" ++ n ++ ".png") extendedImg

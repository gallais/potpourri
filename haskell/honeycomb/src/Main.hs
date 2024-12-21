{-# LANGUAGE MultiWayIf #-}

module Main where

import Codec.Picture
import System.Environment
import System.Exit

inputFile :: IO String
inputFile = getArgs >>= \case
  [fp] -> pure fp
  _ -> die "Invalid arguments: expected a single filename"

averaging :: [PixelYCbCr8] -> PixelYCbCr8
averaging [] =  PixelYCbCr8 0 0 0
averaging pxs = PixelYCbCr8 (finalise x) (finalise y) (finalise z)

  where
    n = length pxs
    finalise x = fromIntegral (x `div` n)
    combine x x' = x + fromIntegral x'
    (x,y,z) = loop 0 0 0 pxs
    loop x y z [] = (x, y, z)
    loop x y z (PixelYCbCr8 x' y' z' : pxs)
      = loop (combine x x') (combine y y') (combine z z') pxs

radius :: Int
radius = 80

pixelsAt :: Pixel x => Image x -> [(Int, Int)] -> [x]
pixelsAt img ijs = uncurry (pixelAt img) <$> filter inRange ijs
  where
    w = imageWidth img
    h = imageHeight img
    inRange (x, y) = (0 <= x && 0 <= y && x < w && y < h)

neighbourhood :: Pixel x => Image x -> Int -> Int -> [x]
neighbourhood img i j
  = pixelsAt img
  [ (x, y)
  | offx <- range
  , offy <- range
  , let x = i + offx
  , let y = j + offy
  ]
  where
    range = [-radius..radius]

square :: Pixel x => Image x -> Int -> Int -> [x]
square img i j
  = pixelsAt img
  [ (x, y)
  | offx <- range
  , offy <- range
  , let x = i + offx
  , let y = j + offy
  ]
  where
    range = [0..2*radius-1]

losange :: Pixel x => Image x -> Int -> Int -> [x]
losange img i j = pixelsAt img
  [ (x, y)
  | offx <- range
  , offy <- range
  , let x = i + offx
  , let y = j + offy
  , abs offx + abs offy <= radius
  ]
  where
    range = [-radius..radius]

blur :: Image PixelYCbCr8 -> Image PixelYCbCr8
blur img = generateImage f (imageWidth img) (imageHeight img)

  where
    f i j = averaging (neighbourhood img i j)

grid :: Image PixelYCbCr8 -> Image PixelYCbCr8
grid img = generateImage blowup (w - w `mod` k) (h - h `mod` k)

  where
   w = imageWidth img
   h = imageHeight img
   k = 2 * radius
   resize x = x `div` k
   sampled = generateImage sample (resize w) (resize h)
   sample i j = averaging (square img (i * k) (j * k))
   blowup i j = pixelAt sampled (i `div` k) (j `div` k)

pave :: Image PixelYCbCr8 -> Image PixelYCbCr8
pave img = generateImage blowup w' h'

  where
   w = imageWidth img
   h = imageHeight img
   w' = (w - w `mod` k) `div` 2
   h' = (h - h `mod` k) `div` 2
   k = radius
   resize x = 2 * (1 + x `div` k)
   sampled = generateImage sample (resize w) (resize h)
   sample i j = averaging (square img (i * k) (j * k))
   blowup i j =
     let x = 1 + 2 * (i `div` k) in
     let y = 1 + 2 * (j `div` k) in
     let offi  = i `mod` k in
     let offj  = j `mod` k in
     let offi1 = k - offi in
     let offj1 = k - offj in
     let (x', y') =
           if | offi  + offj  < k `div` 2 -> (x-1, y-1)
              | offi  + offj1 < k `div` 2 -> (x-1, y+1)
              | offi1 + offj  < k `div` 2 -> (x+1, y-1)
              | offi1 + offj1 < k `div` 2 -> (x+1, y+1)
              | otherwise -> (x, y)
    in pixelAt sampled x' y'

main :: IO ()
main = do
  fp <- inputFile
  readImage fp >>= \case
    Left err -> die err
    Right (ImageYCbCr8 img) ->
      saveJpgImage 100 "output.jpg" (ImageYCbCr8 (pave img))
    _ -> die "Wrong filetype"

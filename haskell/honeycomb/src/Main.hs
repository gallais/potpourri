{-# LANGUAGE MultiWayIf #-}

module Main where

import Codec.Picture
import System.Environment (getArgs)
import System.Exit (die)
import Data.Foldable (for_)
import Text.Read (readMaybe)

data Config = Config
  { radius :: Int
  , files  :: [FilePath]
  }

parseConfig :: Config -> [String] -> Either String Config
parseConfig cfg [] = pure cfg
parseConfig cfg ("-r" : r : rest) = case readMaybe r of
  Nothing -> Left ("Invalid radius argument: " ++ r ++ ".")
  Just r -> parseConfig (cfg { radius = r }) rest
parseConfig cfg ("-r" : []) = Left "Missing radius argument."
parseConfig cfg (fp : rest) = parseConfig (cfg { files = fp : files cfg }) rest

getConfig :: IO Config
getConfig = do
  args <- getArgs
  case parseConfig (Config 80 []) args of
    Left err -> die err
    Right cfg -> pure cfg

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

pixelsAt :: Pixel x => Image x -> [(Int, Int)] -> [x]
pixelsAt img ijs = uncurry (pixelAt img) <$> filter inRange ijs
  where
    w = imageWidth img
    h = imageHeight img
    inRange (x, y) = (0 <= x && 0 <= y && x < w && y < h)

neighbourhood :: Pixel x => Int -> Image x -> Int -> Int -> [x]
neighbourhood r img i j
  = pixelsAt img
  [ (x, y)
  | offx <- range
  , offy <- range
  , let x = i + offx
  , let y = j + offy
  ]
  where
    range = [-r..r]

square :: Pixel x => Int -> Image x -> Int -> Int -> [x]
square r img i j
  = pixelsAt img
  [ (x, y)
  | offx <- range
  , offy <- range
  , let x = i + offx
  , let y = j + offy
  ]
  where
    range = [0..2*r-1]

losange :: Pixel x => Int -> Image x -> Int -> Int -> [x]
losange r img i j = pixelsAt img
  [ (x, y)
  | offx <- range
  , offy <- range
  , let x = i + offx
  , let y = j + offy
  , abs offx + abs offy <= r
  ]
  where
    range = [-r..r]

blur :: Int -> Image PixelYCbCr8 -> Image PixelYCbCr8
blur r img = generateImage f (imageWidth img) (imageHeight img)

  where
    f i j = averaging (neighbourhood r img i j)

grid :: Int -> Image PixelYCbCr8 -> Image PixelYCbCr8
grid r img = generateImage blowup (w - w `mod` k) (h - h `mod` k)

  where
   w = imageWidth img
   h = imageHeight img
   k = 2 * r
   resize x = x `div` k
   sampled = generateImage sample (resize w) (resize h)
   sample i j = averaging (square r img (i * k) (j * k))
   blowup i j = pixelAt sampled (i `div` k) (j `div` k)

pave :: Int -> Image PixelYCbCr8 -> Image PixelYCbCr8
pave r img = generateImage blowup w' h'

  where
   w = imageWidth img
   h = imageHeight img
   w' = (w - w `mod` k) `div` 2
   h' = (h - h `mod` k) `div` 2
   k = r
   resize x = 2 * (1 + x `div` k)
   sampled = generateImage sample (resize w) (resize h)
   sample i j = averaging (square r img (i * k) (j * k))
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
  cfg <- getConfig
  for_ (files cfg) $ \ fp -> readImage fp >>= \case
    Left err -> die err
    Right (ImageYCbCr8 img) ->
      saveJpgImage 100 ("modified-" ++ fp) (ImageYCbCr8 (pave (radius cfg) img))
    _ -> die "Wrong filetype"

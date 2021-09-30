module Main where

import Data.Foldable
import Diagrams.Prelude
import Diagrams.Backend.Cairo.CmdLine

import Debug.Trace

centerDot :: Diagram B
centerDot = circle 0.5 # fc red

data Label = Label
  { label  :: String
  , posX   :: Double
  , posY   :: Double
  , parity :: Bool
  }

boxed :: Label -> Diagram B
boxed Label{..} = foldl1 atop
  [ text label
  , rect 2 {-(fromIntegral 2(length label))-} 1.5 # fc lightgrey # lw none
  ]

flipTo :: Bool -> Double
flipTo b = if b then 1 else (-1)

atStep :: Int -> Label -> Diagram B
atStep n lbl@Label{..}
  = let ratX  = posX / abs posY in
    let ratY  = posY / abs posX in
    let posX' = posX + 0.25 * fromIntegral n * ratX in
    let posY' = posY + 0.25 * fromIntegral n * ratY in
    if posX' < -11 || posX' > 11 then mempty else
    if posY' < -6 || posY' > 6 then mempty else
    translateX posX' $ translateY posY'
    $ rotateBy (product [ signum (fromIntegral n)
                        , flipTo parity
                        , (-1)^n
                        , 1/32 ])
               (boxed lbl)

myDiagram :: String -> String -> Int -> Diagram B
myDiagram fun typ n = fold
  [ -- declaration fun : typ
    atStep n $ Label fun (-7.5) 3 False
  , translateX (-4.5) $ translateY 3 $ text ": Env"
  , atStep n $ Label typ (-1.5) 3 True
  , translateX 3 $ translateY 3 $ text "→ Tm → Tm"
  -- equation fun (f $ t) = ...
  , atStep n $ Label fun (-7.5) 1 False
  , translateX (-4) $ translateY 1 $ text "(f $ t) ="
  , atStep n $ Label fun (-0.5) 1 False
  , translateX 1.5 $ translateY 1 $ text "f $ "
  , atStep n $ Label fun 3.5 1 False
  , translateX 5 $ translateY 1 $ text "t"
  , rect 20 10 # fc white
  ] # clipped (rect 20 10)


reel :: [[Diagram B]]
reel =
  let cols = [0..5]; rows = [0..1]; sloc = reverse cols; swor = reverse rows in
   ((myDiagram "ren" "Var" 0 <$ cols) <$ [""])
   ++ map (\ n -> map (myDiagram "ren" "Var" . (5*n+)) cols) rows
   ++ map (\ n -> map (myDiagram "sub" "Tm" . (5*n+)) sloc) swor
   ++ ((myDiagram "sub" "Tm" 0 <$ cols) <$ [""])

script :: Diagram B
script = foldl1 (===) $ map (foldl1 (|||)) reel

main :: IO ()
main = gifMain $ map (, 20) $ concat reel

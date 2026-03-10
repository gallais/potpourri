module Main where

import Data.Function (on)
import Data.List (groupBy, intercalate)
import Data.Maybe (fromMaybe, fromJust, mapMaybe)
import Text.Read (readMaybe)

padleft :: Int -> Char -> String -> String
padleft l c str =
  let w = length str in
  if w < l then replicate (l - w) c ++ str else str

data Entry a = Entry
  { year  :: !Int
  , month :: !Int
  , day   :: !Int
  , hour  :: !Int
  , value :: a
  } deriving (Functor)

displayEntry :: Entry String -> String
displayEntry (Entry y m d h v) = concat
  [ padleft 4 '0' (show y)
  , "-", padleft 2 '0' (show m)
  , "-", padleft 2 '0' (show d)
  , "T", padleft 2 '0' (show h)
  , ",", v ]

parseEntry :: String -> Maybe (Entry Float)
parseEntry
  ( y4:y3:y2:y1
  : '-':m2:m1
  : '-':d2:d1
  : 'T':h2:h1
  : ':':_:_
  : ',' : tmp)
  = Entry
    <$> readMaybe [y4,y3,y2,y1]
    <*> readMaybe [m2,m1]
    <*> readMaybe [d2,d1]
    <*> readMaybe [h2,h1]
    <*> readMaybe tmp
parseEntry _ = Nothing


findMaxTemp :: Ord a => [Entry a] -> Maybe (Entry a)
findMaxTemp [] = Nothing
findMaxTemp (e:es) = Just $ go e es where

  go emax [] = emax
  go emax (e:es)
    | value e > value emax = go e es
    | otherwise = go emax es

findExtremeTemps :: Ord a => [Entry a] -> Maybe (Entry a, Entry a)
findExtremeTemps [] = Nothing
findExtremeTemps (e:es) = Just $ go e e es where

  go emin emax [] = (emin, emax)
  go emin emax (e:es)
    | value e > value emax = go emin e es
    | value e < value emin = go e emax es
    | otherwise = go emin emax es

tr_ :: String -> String
tr_ str = concat ["<tr>", str, "</tr>"]

td_ :: Maybe String -> String -> String
td_ mc str = concat ["<td", fromMaybe "" mc, ">", str, "</td>"]

table_ :: [String] -> String
table_ strs = intercalate "\n" $ "<table cellspacing=\"0\">" : strs ++ ["</table>"]

header :: String
header = unlines $
  [ "<style>"
  , "  table, th, td {"
  , "    border: 1px solid black;"
  , "    border-collapse: collapse;"
  , "  }"
  , "</style>"
  ]

span_ :: String -> String -> String
span_ c str = concat ["<span class=", show c, ">", str, "</span>"]

entry :: (Float, Float) -> Entry Float -> String
entry (vmin, vmax) e =
  let v = value e in
  let pc = show ((v - vmin) / (vmax - vmin)) in
  td_
    (Just $ unwords
       [ ""
       , "style=" ++ show ("background-color: rgba(255, 0, 0, " ++ pc ++ "); width:1ch; height: 1ch")
       , "title=" ++ show (displayEntry $ fmap show e)
       ])
    ""

main :: IO ()
main = do
  txt <- readFile "open-meteo-55.85N4.22W38m.csv"
  putStrLn
  --  $ (header ++)
    $ (\ (mmm, ms) -> let (emin, emax) = fromJust mmm in unlines
        [ "min: " ++ displayEntry (show <$> emin)
        , "<br />"
        , "max: " ++ displayEntry (show <$> emax)
        , "<br />"
        , table_ $ map (tr_ . concatMap (entry (value emin, value emax))) ms
        ])
    $ fmap (groupBy ((==) `on` year))
    $ (\ ms -> (findExtremeTemps ms, ms))
    $ concatMap (mapMaybe findMaxTemp)
    $ map (map (map snd) . groupBy ((==) `on` (`div` (7*24)) `on` fst) . zip [0..])
    $ groupBy ((==) `on` year)
--    $ filter ((== 14) . hour)
--    $ filter ((/= 2026) . year)
--    $ filter ((> 1980) . year)
    $ mapMaybe parseEntry
    $ lines txt

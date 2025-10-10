module Main where

import Control.Monad (void)

import Data.Char (isDigit)
import Data.Foldable (for_)
import System.Directory (doesDirectoryExist, doesFileExist, listDirectory)
import System.FilePath ((</>), splitExtension)
import System.Process (readProcess)
import Text.Read (readMaybe)

withContext :: String -> Either [String] a -> Either [String] a
withContext ctx (Left str) = Left (ctx : map ("  " ++) str)
withContext _ (Right a) = Right a

onDirectories :: FilePath -> (FilePath -> IO ()) -> IO ()
onDirectories fp act = do
  dirs <- listDirectory fp
  for_ dirs $ \ dir -> do
    bDir <- doesDirectoryExist (fp </> dir)
    if bDir then act dir else
      putStrLn (fp </> dir ++ " is not a directory")

onFiles :: FilePath -> (FilePath -> IO ()) -> IO ()
onFiles fp act = do
  files <- listDirectory fp
  for_ files $ \ file -> do
    bFile <- doesFileExist (fp </> file)
    if bFile then act file else
      putStrLn (fp </> file ++ " is not a file")

withRight :: Either [String] a -> (a -> IO ()) -> IO ()
withRight (Left str) _ = putStrLn (unlines str)
withRight (Right a) k = k a

main :: IO ()
main =
  onDirectories "." $ \ root ->
  onDirectories root $ \ dir ->
  withRight (albumInfo root dir) $ \ alInfo ->
  onFiles (root </> dir) $ \ file ->
  withRight (trackInfo alInfo file) $ \ trInfo -> do
  setMetaData alInfo trInfo (root </> dir </> file)

setMetaData
  :: AlbumInfo
  -> TrackInfo
  -> FilePath
  -> IO ()
setMetaData alInfo trInfo fp = case format trInfo of
  MP3 -> void $ readProcess "id3v2"
    [ "-a", artist alInfo
    , "-y", show (year alInfo)
    , "-A", name alInfo
    , "-T", show (track trInfo)
    , "-t", title trInfo
    , fp
    ]
    ""
  FLAC -> void $ readProcess "metaflac"
    [ "--remove-tag=Artist"
    , "--remove-tag=Date"
    , "--remove-tag=Album"
    , "--remove-tag=Title"
    , "--remove-tag=Tracknumber"
    , "--set-tag=" ++ "Artist=" ++ artist alInfo
    , "--set-tag=" ++ "Date=" ++ show (year alInfo)
    , "--set-tag=" ++ "Album=" ++ name alInfo
    , "--set-tag=" ++ "Tracknumber=" ++ show (track trInfo)
    , "--set-tag=" ++ "Title=" ++ title trInfo
    , fp
    ]
    ""


data Format = MP3 | FLAC

data AlbumInfo = AlbumInfo
  { artist :: String
  , year   :: Int
  , name   :: String
  }

data TrackInfo = TrackInfo
  { track  :: Int
  , title  :: String
  , format :: Format
  }

numberAndTitle :: String -> Either [String] (Int, String)
numberAndTitle str@('[':rest) = case span isDigit rest of
  (n, ']':' ':tit) -> do
    num <- case readMaybe n of
      Nothing -> Left [show n ++ " is not a valid number in " ++ show str]
      Just i -> Right i
    pure (num, tit)
  _ -> Left ["Couldn't split " ++ show str ++ " into number and "]
numberAndTitle str = Left [show str ++ " does not start with '['"]

albumInfo :: String -> String -> Either [String] AlbumInfo
albumInfo root dir = withContext ("Looking at artist " ++ root) $ do
  (num, tit) <- numberAndTitle dir
  pure (AlbumInfo root num tit)

trackInfo :: AlbumInfo -> String -> Either [String] TrackInfo
trackInfo al fp
  = withContext ("Looking at artist " ++ artist al)
  $ withContext ("Looking at album " ++ name al)
  $ do let (nm, ext) = splitExtension fp
       fmt <- case ext of
         ".mp3" -> pure MP3
         ".flac" -> pure FLAC
         _ -> Left ["Invalid file extension: " ++ ext]
       (num, tit) <- numberAndTitle nm
       pure (TrackInfo num tit fmt)

module poc.😸 where

import IO.Primitive as Prim
open import Data.Unit
open import IO
open import Coinduction
open import Data.Colist as C
open import Data.List.Base
open import Data.Char.Base using (Char)
open import Data.String.Base as S
open import Function

postulate primGetArgs : Prim.IO (List String)
{-# FOREIGN GHC import System.Environment           #-}
{-# FOREIGN GHC import Data.Text                    #-}
{-# COMPILE GHC primGetArgs = fmap pack <$> getArgs #-}

getArgs : IO (List String)
getArgs = lift primGetArgs

putChar : Char → IO _
putChar c = putStr (S.fromList (c ∷ []))

cat : String → IO _
cat fp = ♯ readFile fp >>= λ cstr →
         ♯ mapM′ putChar cstr

main : Prim.IO _
main = run $ ♯ getArgs >>= λ fps →
             ♯ mapM′ cat (C.fromList fps)

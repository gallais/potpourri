module CyclicListExamples where

import Prelude  (($), Int, Bool, uncurry, (==), (.))
import CyclicList

flist1 :: List Int
flist1 = fromList [1, 2, 4, 5]

clist1 :: List Int
clist1 = cycle 1 [2]

clist2 :: List Int
clist2 = 1 `cons` cycle 2 [3]

clist3 :: List Int
clist3 = cycle 1 [2, 3]

clist4 :: List Int
clist4 = flist1 `append` clist3

unzipzip :: Bool
unzipzip = unzip (uncurry zip (clist1, clist4)) == (clist1, clist4)

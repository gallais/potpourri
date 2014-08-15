module CyclicListFlat where

import Prelude hiding (cycle, reverse)

data CList a =
  CList { prfx :: [ a ]
        , cycl :: [ a ] }

instance Functor CList where
  fmap f xs = CList { prfx = fmap f $ prfx xs
                    , cycl = fmap f $ cycl xs }

cnil :: CList a
cnil = CList { prfx = [], cycl = [] }

cons :: a -> CList a -> CList a
cons x xs = xs { prfx = x : prfx xs }

singleton :: a -> CList a
singleton x = cons x cnil

cycle :: a -> [a] -> CList a
cycle x xs = CList { prfx = [], cycl = x : xs }

isFinite :: CList a -> Bool
isFinite = null . cycl

isCyclic :: CList a -> Bool
isCyclic = not . isFinite

getCycle :: CList a -> [ a ]
getCycle = cycl

getPrefix :: CList a -> [ a ]
getPrefix = prfx

getSupport :: CList a -> [ a ]
getSupport xs = prfx xs ++ cycl xs

cfold :: (a -> b -> b) -> b -> (a -> (b -> b) -> b) -> CList a -> b
cfold c n r xs = foldr c (aux n $ cycl xs) $ prfx xs
  where
    aux p []       = p
    aux p (y : ys) = r y (\ b -> foldr c b ys)

cfold' :: (a -> b -> b) -> b -> CList a -> b
cfold' c n = cfold c n r
  where r a ih = c a $ ih $ r a ih

cfoldFinite :: (a -> b -> b) -> b -> CList a -> Maybe b
cfoldFinite c n = cfold (\ a -> fmap (c a)) (Just n) r
  where r = const $ const Nothing

append :: CList a -> CList a -> CList a
append xs ys = cfold cons ys (\ a ih -> cons a $ ih cnil) xs

length :: Num b => CList a -> Maybe b
length = cfoldFinite (const (+1)) 0

reverse :: CList a -> Maybe (CList a)
reverse = cfoldFinite (flip append . singleton) cnil

instance Show a => Show (CList a) where
  show = cfold (\ a    -> (++) (show a ++ " : ")) "[]"
               (\ a ih -> "rec X. " ++ show a ++ " : " ++ ih "X")

toStream :: CList a -> [ a ]
toStream = cfold' (:) []

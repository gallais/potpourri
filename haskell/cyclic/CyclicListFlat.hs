module CyclicListFlat where

import Prelude hiding (cycle, reverse, take, splitAt, zipWith, and, or, null, repeat)
import Control.Applicative
import qualified Data.List as List
import qualified Control.Monad as Monad

data CList a =
  CList { prfx :: [ a ]
        , cycl :: [ a ] }

data View a = CNil | Cons a (CList a)

rewind :: Eq a => CList a -> CList a
rewind xs = go (List.reverse $ prfx xs) cs []
  where
    cs = List.reverse $ cycl xs
    go []       cs       ds = unsafeCycle (ds ++ List.reverse cs)
    go ps       []       ds = go ps cs []
    go (p : ps) (c : cs) ds
      | p == c    = go ps cs (c : ds)
      | otherwise = CList (List.reverse $ p : ps)
                          (ds ++ List.reverse (c : cs))

cyclic :: Eq a => Int -> [ a ] -> Maybe [ a ]
cyclic n xs =
  let cyc = List.take n xs
      l   = List.length xs
      xss = xs ++ List.take (n * (l `div` n) - l) xs in
  if xss == Monad.join (List.replicate (l `div` n) cyc)
  then Just cyc
  else Nothing

factor :: Eq a => CList a -> CList a
factor xs =
  let l = List.length $ cycl xs in
  case Monad.msum $ flip cyclic (cycl xs) <$> [1..l-1] of
    Nothing  -> xs
    Just cyc -> xs { cycl = cyc }

minimise :: Eq a => CList a -> CList a
minimise = factor . rewind

null :: CList a -> Bool
null xs = List.null (prfx xs) && List.null (cycl xs)

repeat :: a -> CList a
repeat x = CList [] [x]

join :: CList (CList a) -> CList a
join = cfold append cnil crec
  where
    crec x ih =
      let res = x `append` ih cnil in
      if isFinite res && not (null res)
      then unsafeCycle $ prfx res
      else res

observe :: CList a -> View a
observe xs =
  case (prfx xs, cycl xs) of
    (y : ys, zs) -> Cons y $ xs { prfx = ys }
    ([], z : zs) -> Cons z $ xs { prfx = zs }
    ([], []    ) -> CNil

splitAt :: Int -> CList a -> Maybe ([ a ], CList a)
splitAt 0 xs = Just ([], xs)
splitAt n xs | 0 < n =
  case observe xs of
    CNil      -> Nothing
    Cons y ys -> (uncurry $ (,) . (y :)) <$> splitAt (n - 1) ys
splitAt n xs | otherwise = Nothing

unfoldCycleBy :: Int -> [ a ] -> CList a
unfoldCycleBy n xs =
  let l        = List.length xs
      ps       = Monad.join $ List.replicate (n `div` l) xs
      (ys, zs) = List.splitAt (n `mod` l) xs in
  CList { prfx = ps ++ ys, cycl = zs ++ ys }

take :: Int -> CList a -> Maybe [ a ]
take n = (fst <$>) . splitAt n

drop :: Int -> CList a -> Maybe (CList a)
drop n = (snd <$>) . splitAt n

zipWith :: (a -> b -> c) -> CList a -> CList b -> CList c
zipWith f xs ys = go (prfx xs) (prfx ys) (cycl xs) (cycl ys)
  where
    go [] [] [] _  = cnil
    go [] [] _  [] = cnil
    go [] [] ss ts =
      let m  = List.length ss
          n  = List.length ts
          l  = lcm m n
          ms = Monad.join $ List.replicate (l `div` m) ss
          ns = Monad.join $ List.replicate (l `div` n) ts
      in unsafeCycle $ List.zipWith f ms ns
    go ps [] ss ts =
      let ts' = unfoldCycleBy (List.length ps) ts
          pqs = fromList $ List.zipWith f ps (prfx ts')
      in fromList (prfx pqs) `append` go [] [] ss (cycl ts')
    go [] qs ss ts =
      let ss' = unfoldCycleBy (List.length qs) ss
          pqs = fromList $ List.zipWith f (prfx ss') qs
      in fromList (prfx pqs) `append` go [] [] (cycl ss') ts
    go (p : ps) (q : qs) ss ts = cons (f p q) $ go ps qs ss ts

instance Functor CList where
  fmap f xs = CList { prfx = fmap f $ prfx xs
                    , cycl = fmap f $ cycl xs }

instance Functor View where
  fmap _ CNil        = CNil
  fmap f (Cons x xs) = Cons (f x) $ fmap f xs

cnil :: CList a
cnil = CList [] []

cons :: a -> CList a -> CList a
cons x xs = xs { prfx = x : prfx xs }

singleton :: a -> CList a
singleton x = cons x cnil

fromList :: [ a ] -> CList a
fromList xs = CList { prfx = xs, cycl = [] }

cycle :: a -> [a] -> CList a
cycle x xs = CList { prfx = [], cycl = x : xs }

unsafeCycle :: [ a ] -> CList a
unsafeCycle xs@(_ : _) = CList [] xs

isFinite :: CList a -> Bool
isFinite = List.null . cycl

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
cfoldFinite c n xs | isFinite xs = Just $ foldr c n $ prfx xs
cfoldFinite c n xs | otherwise   = Nothing

append :: CList a -> CList a -> CList a
append xs ys | isFinite xs = ys { prfx = prfx xs ++ prfx ys }
append xs ys | otherwise   = xs

length :: Num b => CList a -> Maybe b
length = cfoldFinite (const (+1)) 0

reverse :: CList a -> Maybe (CList a)
reverse = cfoldFinite (flip append . singleton) cnil

toList :: CList a -> Maybe [ a ]
toList xs | isFinite xs = Just $ prfx xs
toList xs | otherwise   = Nothing

head :: CList a -> Maybe a
head = cfold (const . Just) Nothing (const . Just)

and :: CList Bool -> Bool
and = cfold (&&) True (const $ const True)

all :: (a -> Bool) -> CList a -> Bool
all p = and . fmap p

or :: CList Bool -> Bool
or = cfold (||) False (const $ const False)

any :: (a -> Bool) -> CList a -> Bool
any p = or . fmap p

intersperse :: a -> CList a -> CList a
intersperse x xs = CList { prfx = List.intersperse x $ prfx xs
                         , cycl = List.intersperse x $ cycl xs }

unzip :: CList (a, b) -> (CList a, CList b)
unzip xs =
  let (ps, qs) = List.unzip $ prfx xs
      (ss, ts) = List.unzip $ cycl xs
  in (CList ps ss, CList qs ts)

instance Show a => Show (CList a) where
  show = cfold (\ a    -> (++) (show a ++ " : ")) "[]"
               (\ a ih -> "rec X. " ++ show a ++ " : " ++ ih "X")

instance Show a => Show (View a) where
  show CNil        = []
  show (Cons x xs) = show x ++ " : " ++ show xs

instance Eq a => Eq (CList a) where
  xs == ys = and $ zipWith (==) xs ys

instance Eq a => Eq (View a) where
  CNil      == CNil      = True
  Cons x xs == Cons y ys = x == y && xs == ys
  _         == _         = False

instance Monad CList where
  return  = singleton
  m >>= f = join $ fmap f m

toStream :: CList a -> [ a ]
toStream = cfold' (:) []

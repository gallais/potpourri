{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Desc where

import Data.ByteString (ByteString, index, readFile)
import qualified Data.ByteString as B

import Data.Bifunctor
import Data.Bits
import Data.Kind
import Data.Maybe
import Data.Proxy
import Data.String
import Data.Word
import GHC.Exts
import GHC.TypeLits
import Unsafe.Coerce

type family If (b :: Bool) (l :: a) (r :: a) :: a where
  If True l r = l
  If False l r = r

data Desc (b :: Bool) :: * where
  None :: Desc b
  Byte :: Desc b
  Prod :: Desc False -> Desc b -> Desc b
  Rec :: Desc b

type family Static (d :: Desc b) :: Nat where
  Static None = 0
  Static Byte = 1
  Static (Prod d e) = Static d + Static e
  Static Rec = 0

type family Offsets (d :: Desc b) :: Nat where
  Offsets None = 0
  Offsets Byte = 0
  Offsets (Prod d e) = Offsets d + Offsets e
  Offsets (Rec :: Desc b) = If b 0 1

type family Meaning (d :: Desc b) (x :: Type) :: Type where
  Meaning None _ = ()
  Meaning Byte _ = Word8
  Meaning (Prod d e) x = (Meaning d x, Meaning e x)
  Meaning Rec x = x

data Vect (n :: Nat) (a :: Type) :: Type where
  N :: Vect 0 a
  C :: a -> Vect n a -> Vect (1+n) a

deriving instance Functor (Vect n)
deriving instance Foldable (Vect n)

split :: forall m n a. KnownNat m => Vect (m + n) a -> (Vect m a, Vect n a)
split xs = unsafeSplit (natVal (Proxy :: Proxy m)) xs where

  unsafeSplit :: {- m :: -} Integer -> Vect (m + n) a -> (Vect m a, Vect n a)
  unsafeSplit 0 xs = unsafeCoerce (N, xs)
  unsafeSplit n (C hd tl)
    = let (ls, rs) = unsafeSplit (n-1) (unsafeCoerce tl) in
      unsafeCoerce (C hd ls, rs)

tabulate :: forall m a. KnownNat m => (Int -> a) -> Vect m a
tabulate = unsafeTabulate (natVal (Proxy :: Proxy m)) where

  unsafeTabulate :: {- m :: -} Integer -> (Int -> a) -> Vect m a
  unsafeTabulate 0 f = unsafeCoerce N
  unsafeTabulate n f = unsafeCoerce (C (f 0) (unsafeTabulate (n-1) (f.(1+))))

data Constructor
   = (:::)
   { name :: Symbol
   , description :: Desc True
   }
type Data = [Constructor]

type family Names (cs :: Data) :: [Symbol] where
  Names '[] = '[]
  Names (nm ::: _ : cs) = nm : Names cs

type family Name (c :: Constructor) :: Symbol where
  Name (nm ::: _) = nm

type family Description (c :: Constructor) :: Desc True where
  Description (_ ::: d) = d

type family EQ (nm :: Symbol) (nm' :: Symbol) :: Bool where
  EQ nm nm = True
  EQ _ _ = False

type Index cs nm = Index' (Names cs) cs nm

type family ListConstructors (nms :: [Symbol]) :: ErrorMessage where
  ListConstructors [a, b] = Text a :<>: Text ", or " :<>: Text b
  ListConstructors '[a] = Text a
  ListConstructors (a : as) = Text a :<>: Text ", " :<>: ListConstructors as

type family Index' (nms :: [Symbol]) (cs :: Data) (nm :: Symbol) :: Nat where
  Index' nms '[] nm = TypeError
                    (Text nm
                    :<>: Text " is not a valid constructor name, expected one of: "
                    :<>: ListConstructors nms)
  Index' nms (c : cs) nm = If (EQ nm (Name c)) 0 (1 + Index' nms cs nm)

type family Lookup (as :: [a]) (k :: Nat) :: a where
  Lookup (hd : _) 0 = hd
  Lookup (_ : tl) n = Lookup tl (n-1)

type Head cs = Lookup cs 0

data AtIndex (cs :: Data) (c :: Constructor) (nm :: Symbol) (n :: Nat) :: Type where
  Z :: AtIndex (c : cs) c (Name c) 0
  S :: AtIndex cs c nm n -> AtIndex (c' : cs) c nm (1+n)

data MuI (cs :: Data) :: * where
  MkMuI :: KnownNat n
        => AtIndex cs c nm n
        -> Meaning (Description c) (MuI cs)
        -> MuI cs

class HasIndex' cs nm (b :: Bool) where
  hasIndex' :: proxy b -> AtIndex cs (Lookup cs (Index cs nm)) nm (Index cs nm)

hasIndex :: forall nm cs proxy. HasIndex cs nm
         => AtIndex cs (Lookup cs (Index cs nm)) nm (Index cs nm)
hasIndex = hasIndex' @cs @nm (Proxy :: Proxy ((EQ nm (Name (Head cs)))))

type family HasIndex (cs :: Data) (nm :: Symbol) :: Constraint where
  HasIndex cs nm = HasIndex' cs nm (EQ nm (Name (Head cs)))

instance (EQ nm (Name c) ~ False, HasIndex cs nm) => HasIndex' (c : cs) nm False where
  hasIndex' _ = S (unsafeCoerce (hasIndex @nm @cs))

instance nm ~ Name c => HasIndex' (c : cs) nm True where
  hasIndex' _ = Z

type Tree
  = [ "Leaf" ::: None
    , "Node" ::: Prod Rec (Prod Byte Rec)
    ]

leaf :: MuI Tree
leaf = MkMuI (hasIndex @"Leaf") ()

node :: MuI Tree -> Word8 -> MuI Tree -> MuI Tree
node l b r = MkMuI (hasIndex @"Node") (l, (b, r))

example :: MuI Tree
example = node (node (node leaf 1 leaf) 5 leaf)
               10
               (node leaf 20 leaf)

data MuP (cs :: Data)
  = MkMuP
  { muBuffer :: ByteString
  , muPointer :: Int
  }

data MeaningP (d :: Desc b) (cs :: Data)
  = MkMeaningP
  { meaningBuffer :: ByteString
  , meaningPointer :: Int
  , meaningOffsets :: Vect (Offsets d) Int
  }

type family Poke (d :: Desc b) (cs :: Data) :: Type where
  Poke None cs = ()
  Poke Byte cs = Word8
  Poke (Prod d e) cs = (MeaningP d cs, MeaningP e cs)
  Poke Rec cs = MuP cs

type family Layer (d :: Desc b) (cs :: Data) :: Type where
  Layer None cs = ()
  Layer Byte cs = Word8
  Layer (Prod d e) cs = (Layer d cs, Layer e cs)
  Layer Rec cs = MuP cs

class IsDesc (d :: Desc b) where
  poke :: MeaningP d cs -> Poke d cs
  layer :: MeaningP d cs -> Layer d cs

instance IsDesc None where
  poke _ = ()
  layer _ = ()

instance IsDesc Byte where
  poke (MkMeaningP buf ptr offs) = index buf ptr
  layer = poke

instance
  ( KnownNat (Offsets d)
  , KnownNat (Static d)
  , IsDesc d
  , IsDesc e
  ) => IsDesc (Prod d e) where
  poke (MkMeaningP buf ptr offs :: MeaningP (Prod d e) cs)
    = let (loffs, roffs) = split @(Offsets d) offs in
      let offset = sum loffs + fromIntegral (natVal @(Static d) Proxy) in
      (MkMeaningP buf ptr loffs, MkMeaningP buf (ptr + offset) roffs)
  layer = bimap layer layer . poke

instance IsDesc Rec where
  poke (MkMeaningP buf ptr _) = MkMuP buf ptr
  layer = poke

type IsConstructor c
  = ( IsDesc (Description c)
    , KnownNat (Offsets (Description c))
    )

data View (cs :: Data) :: * where
  MkView :: AtIndex cs c nm n
         -> Layer (Description c) cs
         -> View cs

data IsConstructorDict (c :: Constructor) :: Type where
  MkIsConstructorDict :: IsConstructor c => IsConstructorDict c

data AnIndex (cs :: Data) :: Type where
  MkAnIndex :: forall cs c nm n.
    IsConstructorDict c
    -> AtIndex cs c nm n
    -> AnIndex cs

here :: forall c cs. IsConstructor c => AnIndex (c : cs)
here = MkAnIndex MkIsConstructorDict Z

there :: AnIndex cs -> AnIndex (c : cs)
there (MkAnIndex dict v) = MkAnIndex (unsafeCoerce dict) (S v)

type family AllConstructors (cs :: Data) :: Constraint where
  AllConstructors '[] = ()
  AllConstructors (c : cs) = (IsConstructor c, AllConstructors cs)

class AllConstructors cs => IsData (cs :: Data) where
  isIndex :: Int -> Maybe (AnIndex cs)

instance IsData '[] where
  isIndex _ = Nothing

instance (IsData cs, IsConstructor c) => IsData (c : cs) where
  isIndex 0 = pure here
  isIndex n = there <$> isIndex (n-1)

readByte :: ByteString -> Int -> Word8
readByte buf ptr = index buf ptr

readInt64 :: ByteString -> Int -> Int{-64-}
readInt64 buf ptr
  = foldr (\ w i -> fromIntegral w + (i `shiftL` 8)) 0
  $ map (readByte buf . (ptr +)) [0..7] where

readOffsets :: KnownNat n => ByteString -> Int -> Vect n Int
readOffsets buf ptr = tabulate (\ i -> readInt64 buf (ptr + (i * 8)))

view :: forall cs. IsData cs => MuP cs -> View cs
view (MkMuP buf ptr)
  = let cons = readByte buf ptr in
    case isIndex @cs (fromIntegral cons) of
      Nothing -> error "Invalid representation"
      Just (MkAnIndex MkIsConstructorDict (nm :: AtIndex cs c nm n)) ->
        let offs = natVal @(Offsets (Description c)) Proxy in
        let ptr' = ptr + 1 + (fromIntegral offs * 8) in
        MkView nm $
        layer @_ @(Description c) @cs $
        MkMeaningP buf ptr' (readOffsets buf (ptr + 1))

summing :: MuP Tree -> Int
summing ptr = case view ptr of
  -- I could not get a pattern matching using "Leaf" and "Node"
  -- to work (even just using type annotations)
  MkView Z () -> 0
  MkView (S Z) (l, (b, r)) -> summing l + fromIntegral b + summing r

main :: IO ()
main = do
  ptr <- flip MkMuP 0 <$> B.readFile "tmp"
  putStrLn $ show (summing ptr)

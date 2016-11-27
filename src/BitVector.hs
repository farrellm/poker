{-# LANGUAGE DataKinds, TypeFamilies, TypeOperators,
    GeneralizedNewtypeDeriving, StandaloneDeriving,
    MultiParamTypeClasses, FlexibleInstances,
    ScopedTypeVariables, FlexibleContexts,
    UndecidableInstances #-}

module BitVector where

import Data.Bits
import Data.Char (intToDigit)
import Data.List (foldl', intercalate)
import Data.Word
import Data.Proxy
import GHC.TypeLits
import Numeric (showIntAtBase)
import Unsafe.Coerce

type family BVElem (b::Nat) :: * where
  BVElem 1 = Word8
  BVElem 2 = Word8
  BVElem 4 = Word8
  BVElem 8 = Word8
  BVElem 16 = Word16
  BVElem 32 = Word32
  BVElem 64 = Word64

newtype BitVector b n = BitVector { bitVec :: BVElem (b*n) }

-- deriving instance Show (BVElem (b*n)) => Show (BitVector b n)
deriving instance Eq (BVElem (b*n)) => Eq (BitVector b n)
deriving instance Ord (BVElem (b*n)) => Ord (BitVector b n)
deriving instance Bits (BVElem (b*n)) => Bits (BitVector b n)
deriving instance FiniteBits (BVElem (b*n)) => FiniteBits (BitVector b n)
deriving instance Enum (BVElem (b*n)) => Enum (BitVector b n)
deriving instance Real (BVElem (b*n)) => Real (BitVector b n)
deriving instance Integral (BVElem (b*n)) => Integral (BitVector b n)
deriving instance Num (BVElem (b*n)) => Num (BitVector b n)

instance forall b n . (BV b n) => Show (BitVector b n) where
  show v =
    let w = 2
        b = fromIntegral $ natVal (Proxy :: Proxy b)
        n = fromIntegral $ natVal (Proxy :: Proxy n)
        t = showIntAtBase w intToDigit v ""
        bitsPerDigit = logBase 2 $ fromIntegral w
        a = round (fromIntegral b / bitsPerDigit)
        nMissing = round (fromIntegral b * n / bitsPerDigit) - length t
        h = replicate nMissing '0'
        s = h ++ t
    in "BitVector " ++ (intercalate "," $ splitAll a s)
    where splitAll _ [] = []
          splitAll a ls = let (l, s) = splitAt a ls
                          in l : splitAll a s

class (KnownNat b, KnownNat n, KnownNat (b*n),
       Num (BVElem b), Integral (BVElem b),
       Integral (BVElem (b*n)), Bits (BVElem (b*n))) =>
      BV (b::Nat) (n::Nat) where

  empty :: BitVector b n
  empty = zeroBits

  (!) :: BitVector b n -> Int -> BVElem b
  v ! i = let s = fromInteger $ natVal (Proxy :: Proxy b)
          in fromIntegral (v `shift` (-s * i))


instance BV 8 1

instance BV 16 1
instance BV 8 2

instance BV 32 1
instance BV 16 2
instance BV 8 4

instance BV 64 1
instance BV 32 2
instance BV 16 4
instance BV 8 8

-- mask1 :: Word8
-- mask1 = 0x1

-- instance (KnownNat n, KnownNat (1*n),
--           Integral (BVElem (1*n)), Bits (BVElem (1*n))) =>
--          BV 1 n where
--   (BitVector a) ! i = mask1 .&. fromIntegral (a `shift` (-1 * i))

-- mask2 :: Word8
-- mask2 = 0x3

-- instance (KnownNat n, KnownNat (2*n),
--           Integral (BVElem (2*n)), Bits (BVElem (2*n))) =>
--          BV 2 n where
--   (BitVector a) ! i = mask2 .&. fromIntegral (a `shift` (-2 * i))

mask4 :: Word8
mask4 = 0xF

instance BV 4 4 where
  (BitVector a) ! i =
    mask4 .&. fromIntegral (a `shift` (-4 * i))

instance BV 4 16 where
  (BitVector a) ! i =
    mask4 .&. fromIntegral (a `shift` (-4 * i))


reshape :: ((a * b) ~ (c * d))
        => BitVector a b -> BitVector c d
reshape = unsafeCoerce

toList :: forall b n . BV b n
       => BitVector b n -> [BVElem b]
toList v =
    let s = fromInteger $ natVal (Proxy :: Proxy n)
    in map (v !) [0..(s - 1)]

fromList :: forall b n . BV b n
         => [BVElem b] -> BitVector b n
fromList es =
  let s = fromInteger $ natVal (Proxy :: Proxy b)
      f = (\v e -> (v `shift` s) .|. fromIntegral e)
      bv = foldl' f zeroBits es
  in reshape (bv :: BitVector (b*n) 1)

fromElem :: BVElem b -> BitVector b 1
fromElem e = BitVector e

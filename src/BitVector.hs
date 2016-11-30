{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds, TypeFamilies, TypeOperators, FlexibleInstances,
    MultiParamTypeClasses, ScopedTypeVariables, FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving #-}

module BitVector
  (BitVector, Elem, empty, (!), reshape, fromList, toList)
  where

import Data.Bits
import Data.Char (intToDigit)
import Data.List (foldl', intercalate)
import qualified Data.Text.Format as F
import Data.Word
import Data.Proxy
import GHC.TypeLits
import Numeric (showIntAtBase)
import Unsafe.Coerce

type family Elem (b :: Nat) :: * where
        Elem 1 = Word8
        Elem 2 = Word8
        Elem 4 = Word8
        Elem 8 = Word8
        Elem 16 = Word16
        Elem 32 = Word32
        Elem 64 = Word64

newtype BitVector b n = BitVector { bitVec :: Elem (b*n) }

deriving instance Eq (BitVector 8 1)
deriving instance Ord (BitVector 8 1)
deriving instance Bits (BitVector 8 1)
deriving instance FiniteBits (BitVector 8 1)
deriving instance Enum (BitVector 8 1)
deriving instance Real (BitVector 8 1)
deriving instance Integral (BitVector 8 1)
deriving instance Num (BitVector 8 1)

deriving instance Eq (BitVector 16 1)
deriving instance Ord (BitVector 16 1)
deriving instance Bits (BitVector 16 1)
deriving instance FiniteBits (BitVector 16 1)
deriving instance Enum (BitVector 16 1)
deriving instance Real (BitVector 16 1)
deriving instance Integral (BitVector 16 1)
deriving instance Num (BitVector 16 1)

deriving instance Eq (BitVector 32 1)
deriving instance Ord (BitVector 32 1)
deriving instance Bits (BitVector 32 1)
deriving instance FiniteBits (BitVector 32 1)
deriving instance Enum (BitVector 32 1)
deriving instance Real (BitVector 32 1)
deriving instance Integral (BitVector 32 1)
deriving instance Num (BitVector 32 1)

deriving instance Eq (BitVector 64 1)
deriving instance Ord (BitVector 64 1)
deriving instance Bits (BitVector 64 1)
deriving instance FiniteBits (BitVector 64 1)
deriving instance Enum (BitVector 64 1)
deriving instance Real (BitVector 64 1)
deriving instance Integral (BitVector 64 1)
deriving instance Num (BitVector 64 1)

instance (BV b n, Integral (Elem b), Show (Elem b)) =>
         Show (BitVector b n) where
  show v =
    let b = fromIntegral $ natVal (Proxy :: Proxy b)
        vs = map (\i -> showIntAtBase 2 intToDigit i "") .
             reverse $ toList v
        ws = map (padLeft b) vs
    in "BitVector " ++ (intercalate "," ws)
    where padLeft n s = replicate (n - length s) '0' ++ s

empty :: forall b n . (Bits (BitVector (b*n) 1)) => BitVector b n
empty = reshape (zeroBits :: BitVector (b*n) 1)
{-# INLINE empty #-}

class (KnownNat b, KnownNat n,
       Bits (Elem (b*n)), Integral (Elem (b*n)), Num (Elem b)) =>
      BV b n  where
  (!) :: BitVector b n -> Int -> Elem b
  (!) = indexRaw
  {-# INLINE (!) #-}

  indexRaw :: BitVector b n -> Int -> Elem b
  indexRaw v i =
    let b = fromInteger $ natVal (Proxy :: Proxy b)
        (BitVector bits) = reshape v :: BitVector (b*n) 1
    in fromIntegral (bits `shift` (-b * i))
  {-# INLINE indexRaw #-}

{-# SPECIALIZE (!) :: BitVector 16 4 -> Int -> Elem 16 #-}
{-# SPECIALIZE indexRaw :: BitVector 16 4 -> Int -> Elem 16 #-}


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

mask4 :: Word8
mask4 = 0xF

instance BV 4 2 where
  v ! i = mask4 .&. (v `indexRaw` i)

instance BV 4 4 where
  v ! i = mask4 .&. (v `indexRaw` i)

instance BV 4 8 where
  v ! i = mask4 .&. (v `indexRaw` i)

instance BV 4 16 where
  v ! i = mask4 .&. (v `indexRaw` i)


reshape :: ((a * b) ~ (c * d))
        => BitVector a b -> BitVector c d
reshape = unsafeCoerce
{-# INLINE reshape #-}

toList :: forall b n . BV b n
       => BitVector b n -> [Elem b]
toList v =
    let n = fromInteger $ natVal (Proxy :: Proxy n)
    in map (v !) [0..(n - 1)]
{-# SPECIALIZE toList :: BitVector 16 4 -> [Elem 16] #-}

fromList :: forall b n.
            (BV b n, Integral (Elem b)
            ,Num (BitVector (b*n) 1), Bits (BitVector (b*n) 1))
         => [Elem b] -> BitVector b n
fromList es =
  let b = fromInteger $ natVal (Proxy :: Proxy b)
      f = (\v e -> (v `shift` b) .|. fromIntegral e)
      bv = foldl' f (zeroBits :: BitVector (b*n) 1) es
  in reshape bv
{-# SPECIALIZE fromList :: [Elem 16] -> BitVector 16 4 #-}
{-# SPECIALIZE fromList :: [Elem 4] -> BitVector 4 16 #-}

fromElem :: Elem b -> BitVector b 1
fromElem e = BitVector e
{-# INLINE fromElem #-}

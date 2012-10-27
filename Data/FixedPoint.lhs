> {-# LANGUAGE BangPatterns, RankNTypes #-}
> {- |This FixedPoint module implements arbitrary sized fixed point types and
> computations.  This module intentionally avoids converting to 'Integer' for
> computations because one purpose is to allow easy translation to other
> languages to produce stand-alone fixed point libraries.  Instead of using
> 'Integer', elementary long multiplication and long division are implemented
> explicitly along with sqrt, exp, and erf functions that are implemented using
> only primitive operations. -}
>
> module Data.FixedPoint
>       ( -- * Fixedpoint types
>         FixedPoint4816
>       , FixedPoint3232
>       , FixedPoint6464
>       , FixedPoint128128
>       , FixedPoint256256
>       , FixedPoint512512
>       , FixedPoint10241024
>       -- * Common Operations
>       , erf'
>       , exp'
>       , sqrt'
>       , pi'
>       -- * Big Int Types
>       , Int128
>       , Int256
>       , Int512
>       , Int1024
>       , Int2048
>       , Int4096
>       , Int8192
>       -- * Big Word Types
>       , Word128(..)
>       , Word256
>       , Word512
>       , Word576
>       , Word1024
>       , Word1280
>       , Word2048
>       , Word4096
>       , Word8192
>       -- * Type Constructors
>       , GenericFixedPoint(..)
>       , BigInt(..)
>       , BigWord(..)
>       ) where
> import Data.Bits
> import Data.Word
> import Data.Int
> import Foreign.Storable
> import Foreign.Ptr
> import Numeric

This code implements n.m fixed point types allowing for a range from (2^(n-1),-2^(n-1)].
Given a type `GenericFixedPoint flat internal fracBitRepr` the values m and n
are:
  m = bitSize fracBitRepr
  n = bitSize flat - m

The 'Flat' representation is a signed n+m bit value.  The 'Internal' representation should be a 2*(n+m)
unsigned value for use in division.

> -- | GenericFixedPoitn is a type constructor for arbitrarily-sized fixed point
> -- tyes. Take note the first type variable, @flat@, should be a signed int
> -- equal to the size of the fixed point integral plus fractional bits.
> -- The second type variable, @internal@, should be unsigned and twice
> -- as large a bit size as the @flat@ type.  The final type variable,
> -- @fracBitRepr@, should be a data structure of equal bit size to the
> -- fractional bits in the fixed point type.  See the existing type aliases,
> -- such as @FixedPoint4816@, for examples.

> data GenericFixedPoint flat internal fracBitRepr = FixedPoint flat
>               deriving (Eq, Ord)
>
> toFlat (FixedPoint x) = x
> fromFlat = FixedPoint
>
> type FixedPoint20482048 = GenericFixedPoint Int4096 Word8192 Word2048
> type FixedPoint10241024 = GenericFixedPoint Int2048 Word4096 Word1024
> type FixedPoint512512 = GenericFixedPoint Int1024 Word2048 Word512
> type FixedPoint256256 = GenericFixedPoint Int512 Word1024 Word256
> type FixedPoint128128 = GenericFixedPoint Int256 Word512 Word128
> type FixedPoint6464 = GenericFixedPoint Int128 Word256 Word64
> type FixedPoint3232 = GenericFixedPoint Int64 Word128 Word32
> type FixedPoint4816 = GenericFixedPoint Int64 Word128 Word16
>
> toInternal :: (Integral a, Num b) => GenericFixedPoint a b c -> b
> toInternal (FixedPoint a) = fromIntegral a
>
> fromInternal :: (Integral b, Num a) =>  b -> GenericFixedPoint a b c
> fromInternal w = FixedPoint (fromIntegral w)
>
> fracBits :: (Bits c) => GenericFixedPoint a b c -> Int
> fracBits = bitSize . getC
>
> getC :: GenericFixedPoint a b c -> c
> getC = const undefined
>
> instance (Integral a, Integral b, Bits a, Bits b, Bits c) =>
>          Show (GenericFixedPoint a b c) where
>     show =  (show :: Double -> String) . realToFrac
>
> instance (Enum a, Num a, Bits a, Bits c) =>
>          Enum (GenericFixedPoint a b c) where
>     succ (FixedPoint a) = FixedPoint (a + 1)
>     pred (FixedPoint a) = FixedPoint (a - 1)
>     fromEnum f@(FixedPoint a) = fromEnum (a `shiftR` fracBits f)
>     toEnum x = let r = FixedPoint (toEnum x `shiftL` fracBits r) in r
>
> xOR a b = a && not b || not a && b
>


> instance (Ord a, Num a, Bits a, Bits b, Integral a, Integral b, Bits c) =>
>          Num (GenericFixedPoint a b c) where
>
>     {-# SPECIALIZE INLINE (+) :: FixedPoint6464 -> FixedPoint6464 -> FixedPoint6464 #-}
>     {-# SPECIALIZE INLINE (*) :: FixedPoint6464 -> FixedPoint6464 -> FixedPoint6464 #-}
>     {-# SPECIALIZE INLINE (-) :: FixedPoint6464 -> FixedPoint6464 -> FixedPoint6464 #-}
>     (FixedPoint a) + (FixedPoint b) = FixedPoint (a + b)
>     aval@(FixedPoint a) * bval@(FixedPoint b) =
>       let w = (toInternal $ abs aval) * (toInternal $ abs bval)
>           op = if xOR (aval < 0) (bval < 0) then negate else id
>       in op $ fromInternal (w `shiftR` fracBits aval)
>     a - b = a + negate b
>     negate (FixedPoint a) = FixedPoint (negate a)
>     signum (FixedPoint a)  = FixedPoint $ signum a
>     abs (FixedPoint a) = FixedPoint (abs a)
>     fromInteger i = let r = FixedPoint (fromInteger i `shiftL` fracBits r) in r
>
> instance (Ord a, Integral a, Bits a, Num a, Bits b, Integral b, Bits c) =>
>    Fractional (GenericFixedPoint a b c) where
>     aval / bval =
>       let wa = toInternal $ abs aval
>           wb = toInternal $ abs bval
>           wr = ((wa`shiftL` fracBits aval) `div` wb)
>           op =  if xOR (aval < 0) (bval < 0) then negate else id
>       in (op $ fromInternal wr)
>
>     fromRational a =
>       let (r,k)   = properFraction a
>           (rf,_)  = properFraction (abs $ k * 2^(fracBits res))
>           signFix = if a < 0 then negate else id
>           res = FixedPoint ((abs r `shiftL` fracBits res) .|. rf)
>       in signFix res
>
> instance (Integral a, Ord a, Num a, Bits a, Bits b, Integral b, Bits c) =>
>          Real (GenericFixedPoint a b c) where
>       toRational f@(FixedPoint a) 
>               | a < 0     = negate (toRational $ negate f)
>               | otherwise = fromIntegral a / (2^(fracBits f))
>
> instance (Integral a, Bits a, Integral b, Num a, Bits b, Bits c) => 
>       Read (GenericFixedPoint a b c) where
>       readsPrec n s = [ (realToFrac (r::Double), s) | (r,s) <- readsPrec n s]

Now we need some advanced functions (beyond +,-,*,/) on our fixed point type.
Specifically, we want 'exp' (exponentiation with a base of 'e' ~ 2.71), erf (the
"error function"), and square root.  All of these will be implemented by some
form of approximation such as a Taylor series.  We thus parameterize the number
of terms to allow testing / user control over cost and accuracy.

> pi' :: (Integral a, Bits a, Integral b, Num a, Bits b, Bits c) => 
>         GenericFixedPoint a b c
> pi' = realToFrac pi

> -- | The square root operation uses Newton's method but is parameterized by the number
> -- of iterations and stops early if we have arrived at a fixed point (no pun intended).
> -- Suggested iterations: 500 (But it increases with the size of the input!)
> sqrt' :: (Eq a, Integral a, Num a, Bits a, Integral b, Bits b, Bits c) =>
>          Int -> GenericFixedPoint a  b c -> GenericFixedPoint a b c
> sqrt' cnt input = fromFlat (go cnt 1) `shiftL` (fracBits input `div` 2)
>  where
>  a = toFlat input
>  go 0 g = g
>  go i g = 
>       let gNew = ((a`div`g) + g) `div` 2
>       in if gNew == g then g else go (i-1) gNew

The below exp function includes a taylor series (the 'go' function) but that
operation alone looses precision too quickly so we restrict it's use to an
acceptable range.  Outside of that range we depend on the property
e^x = (e^(x/2))^2 to break the problem down.

This could probably be improved using a lookup table.

> exp' :: (Ord a, Fractional a, Eq a) => Int -> a -> a
> exp' 0 a = 1
> exp' n a
>    | not (a > (-1) && a < 1) = let t = exp' n (a/2) in t*t
>    | otherwise               = go 1 1 a
>  where
>  go !i !total !term
>     | i <= n    = let iNew = i + 1 in go iNew (total + term) (term*a/fromIntegral iNew)
>     | otherwise = total

The first error function was a direct Taylor series implementation.  It lost
accuracy too quickly due to the factorial term.  A superior version from
picomath.org uses precomputed values (picomath released the code as public
domain).

> erf' :: (Eq a, Ord a, Num a, Fractional a) => Int -> a -> a
> erf' n x =
>       let a1 = 0.254829592
>           a2 =  -0.284496736
>           a3 = 1.421413741
>           a4 = -1.453152027
>           a5 =  1.061405429
>           p  = 0.3275911
>           sign = if x < 0 then (-1) else 1
>           x' = abs x
>           t = 1 / (1 + p * x')
>           y = 1 -  (((((a5*t + a4)*t) + a3)*t + a2)*t + a1) * t * exp' n (-x'*x');
>       in sign * y
>
> flat1 :: (a -> Int -> a ) -> GenericFixedPoint a b c -> Int 
>       -> GenericFixedPoint a b c
> flat1 op a i = fromFlat . flip op i . toFlat $ a
> flat2 :: (a -> a -> a) -> GenericFixedPoint a b c
>       -> GenericFixedPoint a b c -> GenericFixedPoint a b c
> flat2 op a b = fromFlat (op (toFlat a) (toFlat b))
>
> instance (Ord a, Bits a, Bits b, Integral a, Integral b, Bits c) =>
>          Bits (GenericFixedPoint a b c) where
>       setBit = flat1 setBit
>       (.|.) = flat2 (.|.)
>       xor = flat2 xor
>       (.&.) = flat2 (.&.)
>       complement = fromFlat . complement . toFlat
>       bitSize a = fracBits a * 2
>       isSigned _ = False
>       shiftL = flat1 shiftL
>       shiftR = flat1 shiftR

To implement FixedPoint division without loosing precision large words are
needed to represent our internal state. 

Unlike other word sizes, Word128 is explicitly implemented and unpacked.  It is
suspected that this will result in a performance difference.  Benchmark results
would be interesting.  If this proves to be a big win then implementing the
other Word sizes by generating code using TH, instead of using overloaded type
classes, would be a beneficial task.

> data Word128 = W128 {-# UNPACK #-} !Word64 {-# UNPACK #-} !Word64

> instance Num Word128 where
>       W128 ah al + W128 bh bl =
>               let rl = al + bl
>                   rh = ah + bh + if rl < al then 1 else 0
>               in W128 rh rl
>       W128 ah al - W128 bh bl =
>               let rl = al - bl
>                   rh = ah - bh - if rl > al then 1 else 0
>               in W128 rh rl
>       a * b = go 0 0
>         where
>         go 128 r = r
>         go i   r
>               | testBit b i  = go (i+1) (r + (a `shiftL` i))
>               | otherwise    = go (i+1) r
>       negate a = 0 - a
>       abs a = a
>       signum a = if a > 0 then 1 else 0
>       fromInteger i = W128 (fromIntegral $ i `shiftR` 64) (fromIntegral i)
>
> pointwise op (W128 a b) = W128 (op a) (op b)
> pointwise2 op (W128 a b) (W128 c d) = W128 (op a c) (op b d)
>
> instance Eq Word128 where
>       a == b = EQ == compare a b
>
> instance Bits Word128 where
>       bit i | i >= 64    = W128 (bit $ i - 64) 0
>             | otherwise = W128 0 (bit i)
>       complement = pointwise complement
>       (.&.) = pointwise2 (.&.)
>       (.|.) = pointwise2 (.|.)
>       xor = pointwise2 xor
>       setBit (W128 h l) i
>               | i >= 64   = W128 (setBit h (i - 64)) l
>               | otherwise = W128 h (setBit l i)
>       shiftL (W128 h l) i
>               | i > bitSize l = shiftL (W128 l 0) (i - bitSize l)
>               | otherwise     = W128 ((h `shiftL` i) .|. (l `shiftR` (bitSize l - i))) (l `shiftL` i)
>       shiftR (W128 h l) i 
>               | i > bitSize h = shiftR (W128 0 h) (i - bitSize h)
>               | otherwise     = W128 (h `shiftR` i) ((l `shiftR` i) .|. h `shiftL` (bitSize h - i))
>       isSigned _ = False
>       testBit (W128 h l) i
>               | i >= bitSize l = testBit h (i - bitSize l)
>               | otherwise      = testBit l i
>       bitSize _ = 128
> 
> instance Enum Word128 where
>       toEnum i            = W128 0 (toEnum i)
>       fromEnum (W128 _ l) = fromEnum l
>       pred (W128 h 0) = W128 (pred h) maxBound
>       pred (W128 h l) = W128 h (pred l)
>       succ (W128 h l) = if l == maxBound then W128 (succ h) 0 else W128 h (succ l)
>
> instance Ord Word128 where
>       compare (W128 ah al) (W128 bh bl) = compare (ah,al) (bh,bl)
>
> instance Real Word128 where
>       toRational w = toRational (fromIntegral w :: Integer)
>
> instance Integral Word128 where
>       toInteger (W128 h l) = (fromIntegral h `shiftL` bitSize l) + fromIntegral l
>       divMod = quotRem
>       quotRem a@(W128 ah al) b@(W128 bh bl) =
>               let r = a - q*b
>                   q = go 0 (bitSize a) 0
>               in (q,r)
>        where
>        -- Trivial long division
>        go :: Word128 -> Int -> Word128 -> Word128
>        go t 0 v = if v >=  b then t+1 else t
>        go t i v
>               | v >= b    = go (setBit t i) i' v2
>               | otherwise = go t i' v1
>         where
>         i' = i - 1
>         newBit = if (testBit a i') then 1 else 0
>         v1 = (v `shiftL` 1) .|. newBit
>         v2 = ((v - b) `shiftL` 1) .|. newBit
>
> instance Show Word128 where
>       show = show . fromIntegral
>
> instance Read Word128 where
>       readsPrec i s = let readsPrecI :: Int -> ReadS Integer
>                           readsPrecI = readsPrec
>                       in [(fromIntegral i, str) | (i,str) <- readsPrecI i s]
>
> instance Bounded Word128 where
>       maxBound = W128 maxBound maxBound
>       minBound = W128 minBound minBound

Larger word aliases follow.

> -- |A 256 bit unsigned word
> type Word256 = BigWord Word128 Word128
>
> -- |A 512 bit unsigned word
> type Word512 = BigWord Word256 Word256

> -- |A 576 bit unsigned word
> type Word576 = BigWord Word512 Word64
>
> -- |A 1024 bit unsigned word
> type Word1024 = BigWord Word512 Word512
>
> -- |A 1280 bit unsigned word
> type Word1280 = BigWord Word1024 Word256
>
> -- |A 2048 bit unsigned word
> type Word2048 = BigWord Word1024 Word1024
>
> -- |A 4096 bit unsigned word
> type Word4096 = BigWord Word2048 Word2048
>
> -- |A 8192 bit unsigned word
> type Word8192 = BigWord Word4096 Word4096
>
> -- |A type constuctor allowing construction of @2^n@ bit unsigned words
> -- The type variable represents half the underlying representation, so
> -- @type Foo = BigWord Word13@ would have a bit size of @26 (2*13)@.
> data BigWord a b = BigWord !a !b

> instance (Integral a, Bits a, Num a, Ord a, Bounded a
>          ,Bits b, Num b, Ord b, Integral b, Bounded b)
>          => Num (BigWord a b) where
>       {-# SPECIALIZE instance Num Word256 #-}
>       {-# SPECIALIZE instance Num Word512 #-}
>       {-# SPECIALIZE instance Num Word576 #-}
>       {-# SPECIALIZE instance Num Word1024 #-}
>       {-# SPECIALIZE instance Num Word1280 #-}
>       {-# SPECIALIZE instance Num Word2048 #-}
>       {-# SPECIALIZE instance Num Word4096 #-}
>       {-# SPECIALIZE instance Num Word8192 #-}
>       BigWord ah al + BigWord bh bl =
>               let rl = al + bl
>                   rh = ah + bh + if rl < al then 1 else 0
>               in BigWord rh rl
>       BigWord ah al - BigWord bh bl =
>               let rl = al - bl
>                   rh = ah - bh - if rl > al then 1 else 0
>               in BigWord rh rl
>       a * b = go 0 0
>         where
>         go i r
>               | i == bitSize r = r
>               | testBit b i    = go (i+1) (r + (a `shiftL` i))
>               | otherwise      = go (i+1) r
>       negate a = 0 - a
>       abs a = a
>       signum a = if a > 0 then 1 else 0
>       fromInteger i =
>               let r@(BigWord _ b) = BigWord (fromIntegral $ i `shiftR` (bitSize b)) (fromIntegral i)
>               in r
>
> pointwiseBW :: (Bits b, Bits c)
>             => (forall a. Bits a => (a -> a)) -> BigWord b c -> BigWord b c
> pointwiseBW op (BigWord a b) = BigWord (op a) (op b)
> pointwiseBW2 :: (Bits b, Bits c)
>              => (forall a. Bits a => (a -> a -> a))
>              -> BigWord b c -> BigWord b c -> BigWord b c
> pointwiseBW2 op (BigWord a b) (BigWord c d) = BigWord (op a c) (op b d)
>
> instance (Ord a, Ord b) => Eq (BigWord a b) where
>       a == b = EQ == compare a b
>
> instance (Ord a, Bits a, Integral a, Bounded a
>          ,Ord b, Bits b, Integral b, Bounded b) => Bits (BigWord a b) where
>       {-# SPECIALIZE instance Bits Word256 #-}
>       {-# SPECIALIZE instance Bits Word512 #-}
>       {-# SPECIALIZE instance Bits Word576 #-}
>       {-# SPECIALIZE instance Bits Word1024 #-}
>       {-# SPECIALIZE instance Bits Word1280 #-}
>       {-# SPECIALIZE instance Bits Word2048 #-}
>       {-# SPECIALIZE instance Bits Word4096 #-}
>       {-# SPECIALIZE instance Bits Word8192 #-}
>       bit i | i >= bitSize b = r1
>             | otherwise      = r2
>        where r1@(BigWord _ b) = BigWord (bit $ i - bitSize b) 0
>              r2 = BigWord 0 (bit i)
>       complement = pointwiseBW complement
>       (.&.) = pointwiseBW2 (.&.)
>       (.|.) = pointwiseBW2 (.|.)
>       xor   = pointwiseBW2 xor
>       setBit (BigWord h l) i
>               | i >= bitSize l = BigWord (setBit h (i-bitSize l)) l
>               | otherwise      = BigWord h (setBit l i)
>       shiftL b i = fromIntegral
>                  . (`shiftL` i)
>                  . (id :: Integer -> Integer)
>                  . fromIntegral $ b
>               -- | i > bitSize l = shiftL (BigWord (fromIntegral l) 0) (i - bitSize l)
>               -- | otherwise     = BigWord ((h `shiftL` i) .|. (fromIntegral (l `shiftR` (bitSize l - i)))) (l `shiftL` i)
>       shiftR b i = fromIntegral
>                  . (`shiftR` i)
>                  . (id :: Integer -> Integer)
>                  . fromIntegral $ b
>               -- | i > bitSize h = shiftR (BigWord 0 h) (i - bitSize h)
>               -- | otherwise     = BigWord (h `shiftR` i) ((l `shiftR` i) .|. fromIntegral (h `shiftL` (bitSize h - i)))
>       isSigned _ = False
>       testBit (BigWord h l) i
>               | i >= bitSize l = testBit h (i - bitSize l)
>               | otherwise      = testBit l i
>       bitSize ~(BigWord h l) = bitSize h + bitSize l
>
> instance (Bounded a, Eq a, Num a, Enum a, Bounded b, Eq b, Num b, Enum b)
>          => Enum (BigWord a b) where
>       {-# SPECIALIZE instance Enum Word256 #-}
>       {-# SPECIALIZE instance Enum Word512 #-}
>       {-# SPECIALIZE instance Enum Word576 #-}
>       {-# SPECIALIZE instance Enum Word1024 #-}
>       {-# SPECIALIZE instance Enum Word1280 #-}
>       {-# SPECIALIZE instance Enum Word2048 #-}
>       {-# SPECIALIZE instance Enum Word4096 #-}
>       {-# SPECIALIZE instance Enum Word8192 #-}
>       toEnum i = BigWord 0 (toEnum i)
>       fromEnum (BigWord _ l) = fromEnum l
>       pred (BigWord h 0) = BigWord (pred h) maxBound
>       pred (BigWord h l) = BigWord h (pred l)
>       succ (BigWord h l) = if l == maxBound then BigWord (succ h) 0 else BigWord h (succ l)
>
> instance (Bounded a, Bounded b) => Bounded (BigWord a b) where
>       {-# SPECIALIZE instance Bounded Word256 #-}
>       {-# SPECIALIZE instance Bounded Word512 #-}
>       {-# SPECIALIZE instance Bounded Word576 #-}
>       {-# SPECIALIZE instance Bounded Word1024 #-}
>       {-# SPECIALIZE instance Bounded Word1280 #-}
>       {-# SPECIALIZE instance Bounded Word2048 #-}
>       {-# SPECIALIZE instance Bounded Word4096 #-}
>       {-# SPECIALIZE instance Bounded Word8192 #-}
>       maxBound = BigWord maxBound maxBound
>       minBound = BigWord minBound minBound
>
> instance (Ord a, Ord b) => Ord (BigWord a b) where
>       {-# SPECIALIZE instance Ord Word256 #-}
>       {-# SPECIALIZE instance Ord Word512 #-}
>       {-# SPECIALIZE instance Ord Word576 #-}
>       {-# SPECIALIZE instance Ord Word1024 #-}
>       {-# SPECIALIZE instance Ord Word1280 #-}
>       {-# SPECIALIZE instance Ord Word2048 #-}
>       {-# SPECIALIZE instance Ord Word4096 #-}
>       {-# SPECIALIZE instance Ord Word8192 #-}
>       compare (BigWord a b) (BigWord c d) = compare (a,b) (c,d)
>
> instance (Bits a, Real a, Bounded a, Integral a
>          , Bits b, Real b, Bounded b, Integral b)
>          => Real (BigWord a b) where
>       toRational w = toRational (fromIntegral w :: Integer)
>
> instance (Bounded a, Integral a, Bits a
>          ,Bounded b, Integral b, Bits b) => Integral (BigWord a b) where
>       {-# SPECIALIZE instance Integral Word256 #-}
>       {-# SPECIALIZE instance Integral Word512 #-}
>       {-# SPECIALIZE instance Integral Word576 #-}
>       {-# SPECIALIZE instance Integral Word1024 #-}
>       {-# SPECIALIZE instance Integral Word1280 #-}
>       {-# SPECIALIZE instance Integral Word2048 #-}
>       {-# SPECIALIZE instance Integral Word4096 #-}
>       {-# SPECIALIZE instance Integral Word8192 #-}
>       toInteger (BigWord h l) = (fromIntegral h `shiftL` bitSize l) + fromIntegral l
>       divMod = quotRem
>       quotRem a b =
>               let r = a - q * b
>                   q = go 0 (bitSize a) 0
>               in (q, r)
>        where
>        -- go :: BigWord a b -> Int -> BigWord a b -> BigWord a b
>        go t 0 v = if v >= b then t + 1 else t
>        go t i v
>               | v >= b    = go (setBit t i) i' v2
>               | otherwise = go t i' v1
>         where
>         i' = i - 1
>         newBit = if (testBit a i') then 1 else 0
>         v1 = (v `shiftL` 1) .|. newBit
>         v2 = ((v-b) `shiftL` 1) .|. newBit
>
> instance (Bounded a, Bits a, Integral a, Bounded b, Bits b, Integral b)
>          => Show (BigWord a b) where
>       show = show . fromIntegral
>
> instance (Integral a, Num a, Bits a, Ord a, Bounded a
>          ,Integral b, Num b, Bits b, Ord b, Bounded b)
>          => Read (BigWord a b) where
>       readsPrec i s = let readsPrecI :: Int -> ReadS Integer
>                           readsPrecI = readsPrec
>                       in [(fromIntegral i, str) | (i,str) <- readsPrecI i s]
>

For fixed point, the flat representation needs to be signed.

> -- |A 128 bit int (signed)
> type Int128 = BigInt Word128
> -- |A 256 bit int (signed)
> type Int256 = BigInt Word256
> -- |A 512 bit int (signed)
> type Int512 = BigInt Word512
> -- |A 1024 bit int (signed)
> type Int1024 = BigInt Word1024
> -- |A 2048 bit int (signed)
> type Int2048 = BigInt Word2048
> -- |A 4096 bit int (signed)
> type Int4096 = BigInt Word4096
> -- |A 8192 bit int (signed)
> type Int8192 = BigInt Word8192
>
> -- |A type constructor for building 2^n bit signed ints.
> -- BigInt is normally just used as a wrapper around BigWord
> -- since twos-complement arithmatic is the same, we simply
> -- need to provide alternate show, read, and comparison operations.
> newtype BigInt a = BigInt { unBI :: a }
>
> instance (Ord a, Bits a) => Ord (BigInt a) where
>       compare (BigInt a) (BigInt b)
>         | testBit a (bitSize a - 1) = if testBit b (bitSize b - 1)
>                                               then compare a b  -- a and b are negative
>                                               else LT           -- a is neg, b is non-neg
>         | testBit b (bitSize b - 1) = GT -- a non-negative, b is negative
>         | otherwise = compare a b -- a and b are non-negative
>
> instance (Eq a) => Eq (BigInt a) where
>       BigInt a == BigInt b = a == b
>
> instance (Show a, Num a, Bits a, Ord a) => Show (BigInt a) where
>       show i@(BigInt a)
>         | i < 0 = '-' : show (complement a + 1)
>         | otherwise = show a
>
> instance (Num a, Bits a, Ord a) => Read (BigInt a) where
>       readsPrec i s = let readsPrecI :: Int -> ReadS Integer
>                           readsPrecI = readsPrec
>                       in [(fromIntegral i, str) | (i,str) <- readsPrecI i s]
>
> instance (Num a, Bits a, Ord a) => Num (BigInt a) where
>       (BigInt a) + (BigInt b) = BigInt (a+b)
>       (BigInt a) - (BigInt b) = BigInt (a-b)
>       (BigInt a) * (BigInt b) = BigInt (a*b)
>       negate (BigInt a) = BigInt (complement a + 1)
>       signum a = if a < 0 then -1 else if a > 0 then 1 else 0
>       abs a = if a < 0 then negate a else a
>       fromInteger i = if i < 0 then negate (BigInt $ fromInteger (abs i))
>                                else BigInt (fromInteger i)
>
> instance (Bits a, Ord a) => Bits (BigInt a) where
>       (.&.) a b = BigInt (unBI a .&. unBI b)
>       (.|.) a b = BigInt (unBI a .|. unBI b)
>       xor a b   = BigInt (unBI a `xor` unBI b)
>       complement = BigInt . complement . unBI
>       shiftL a i = BigInt . (`shiftL` i) . unBI $ a
>       shiftR a i = (if a < 0  then \x -> foldl setBit x [bitSize a-1, bitSize a - 2 .. bitSize a - i]
>                               else id)
>                  . BigInt 
>                  . (`shiftR` i) 
>                  . unBI
>                  $ a
>       bit = BigInt . bit
>       setBit a i = BigInt . (`setBit` i) . unBI $ a
>       testBit a i = (`testBit` i) . unBI $ a
>       bitSize (BigInt a) = bitSize a
>       isSigned _ = True
>
> instance (Bits a, Ord a, Integral a, Bounded a, Num a) => Enum (BigInt a) where
>       toEnum i = fromIntegral i
>       fromEnum i = fromIntegral i
>       pred a | a > minBound = (a - 1)
>       succ a | a < maxBound = (a + 1)
>
> instance (Integral a, Bits a, Bounded a) => Integral (BigInt a) where
>       toInteger i@(BigInt h) = (if i < 0 then negate else id) (toInteger h)
>       quotRem a b =
>               let (BigInt ah) = abs a
>                   (BigInt bh) = abs b
>                   (q1,r1) = quotRem ah bh
>               in if a < 0 && b < 0
>                       then (BigInt q1, negate $ BigInt r1)
>                       else if a < 0
>                               then (negate $ BigInt q1, negate $ BigInt r1)
>                               else if b < 0
>                                       then (negate $ BigInt q1, BigInt r1)
>                                       else (BigInt q1, BigInt r1)
>
> instance (Real a, Bounded a, Integral a, Bits a) => Real (BigInt a) where
>       toRational = fromIntegral
>
>
> instance (Bounded a, Ord a, Bits a) => Bounded (BigInt a) where
>       minBound = let r = fromIntegral (negate (2^ (bitSize r - 1))) in r
>       maxBound = let r = fromIntegral (2^(bitSize r - 1) - 1) in r
>
> instance (Storable a) => Storable (BigInt a) where
>       sizeOf ~(BigInt a) = sizeOf a
>       alignment ~(BigInt a) = alignment a
>       peekElemOff ptr i = fmap BigInt (peekElemOff (castPtr ptr) i)
>       pokeElemOff ptr i (BigInt a) = pokeElemOff (castPtr ptr) i a
>
> instance (Storable a, Storable b) => Storable (BigWord a b) where
>       sizeOf ~(BigWord a b) = sizeOf a + sizeOf b
>       alignment ~(BigWord a b) = max (alignment a) (alignment b)
>       peek ptr = do
>               let p1 = castPtr ptr
>               a <- peek p1
>               let p2 = castPtr (plusPtr p1 (sizeOf a))
>               b <- peek p2
>               return (BigWord a b)
>       poke ptr (BigWord a b) = do
>               let p1 = castPtr ptr
>               poke p1 a
>               let p2 = castPtr (plusPtr p1 (sizeOf a))
>               poke p2 b
>
> instance Storable Word128 where
>       sizeOf ~(W128 a b) = sizeOf a + sizeOf b
>       alignment ~(W128 a b) = max (alignment a) (alignment b)
>       peek ptr = do
>               let p1 = castPtr ptr
>               a <- peek p1
>               let p2 = castPtr $ plusPtr p1 (sizeOf a)
>               b <- peek p2
>               return (W128 a b)
>       poke ptr (W128 a b) = do
>               let p1 = castPtr ptr
>               poke p1 a
>               let p2 = castPtr $ plusPtr p1 (sizeOf a)
>               poke p2 b
>
> instance Storable flat => Storable (GenericFixedPoint flat i r) where
>       sizeOf ~(FixedPoint x) = sizeOf x
>       alignment ~(FixedPoint x) = sizeOf x
>       peek ptr = fmap FixedPoint $ peek (castPtr ptr)
>       poke ptr (FixedPoint x) = poke (castPtr ptr) x

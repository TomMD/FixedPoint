{-# Language ExistentialQuantification, TypeSynonymInstances, FlexibleInstances #-}
import Data.FixedPoint
import Test.QuickCheck
import Control.Monad
import Debug.Trace
import Data.Number.Erf
import Control.Applicative

-- type FixedPoint = FixedPoint128128
type FixedPoint = FixedPoint128128

instance Arbitrary FixedPoint6464 where
        arbitrary = fmap FixedPoint arbitrary

instance Arbitrary Word128 where
        arbitrary = W128 <$> arbitrary <*> arbitrary

instance (Arbitrary a, Arbitrary b) => Arbitrary (BigWord a b) where
        arbitrary = BigWord <$> arbitrary <*> arbitrary 

instance Arbitrary a => Arbitrary (BigInt a) where
        arbitrary = fmap BigInt arbitrary

approx :: (Double -> Double -> Double) -> (FixedPoint -> FixedPoint -> FixedPoint) -> Double -> Double -> Property
approx op po a b =
        let x = po (realToFrac a) (realToFrac b)
            y = op a b
        in aeq y (realToFrac x)

approx1 :: (Double -> Double) -> (FixedPoint -> FixedPoint) -> Double -> Property
approx1 op po a =
        let x = op a
            y = po (realToFrac a :: FixedPoint)
        in aeq x (realToFrac y)

aeq a b = logBase 2 a < 63 ==> let e = 0.001 in if abs (a - b) < e then True else False -- trace (show (a,b)) False

propSub, propMul, propAdd :: Double -> Double -> Property
propAdd = approx (+) (+)
propSub = approx (-) (-)
propMul = approx (*) (*)

propDiv :: Double -> Double -> Property
propDiv a b = b /= 0 ==> approx (/) (/) a b

propConv :: Double -> Bool
propConv d = (toRational (realToFrac d :: FixedPoint)) == (toRational d)

propErf :: Double -> Property
propErf = approx1 erf (erf' 50)

propExp :: Double -> Property
propExp x = x < 30 ==> approx1 exp (exp' 50) x

propSqrt :: Double -> Property
propSqrt = approx1 sqrt (sqrt' 500)

data Test = forall a. Testable a =>  T String a
testFP = [T "sub" propSub, T "add" propAdd, T "div" propDiv, T "mul" propMul
        ,T "conv" propConv, T "erf" propErf, T "exp" propExp, T "sqrt" propSqrt]

addW256, subW256, mulW256 :: Word256 -> Word256 -> Bool
addW256 a b =  a + b == (fromIntegral a + fromIntegral b)
subW256 a b = a - b == (fromIntegral a - fromIntegral b)
mulW256 a b = a * b == (fromIntegral a * fromIntegral b)

divW256,remW256,modW256,quotW256 :: Word256 -> Word256 -> Property
divW256 a b = b /= 0 ==> a `div` b == fromIntegral a `div` fromIntegral b
remW256 a b = b /= 0 ==> a `rem` b == fromIntegral a `rem` fromIntegral b
modW256 a b = b /= 0 ==> a `mod` b == fromIntegral a `mod` fromIntegral b
quotW256 a b = b /= 0 ==> a `quot` b == fromIntegral a `quot` fromIntegral b

testW256 =
        [ T "subW256" subW256
        , T "addW256"  addW256
        , T "mulW256"  mulW256
        , T "divW256"  divW256
        , T "remW256" remW256
        , T "modW256" modW256
        , T "quotW256" quotW256
        ]

addW128, subW128, mulW128 :: Word128 -> Word128 -> Bool
addW128 a b =  a + b == (fromIntegral a + fromIntegral b)
subW128 a b = a - b == (fromIntegral a - fromIntegral b)
mulW128 a b = a * b == (fromIntegral a * fromIntegral b)

divW128,remW128,modW128,quotW128 :: Word128 -> Word128 -> Property
divW128 a b = b /= 0 ==> a `div` b == fromIntegral a `div` fromIntegral b
remW128 a b = b /= 0 ==> a `rem` b == fromIntegral a `rem` fromIntegral b
modW128 a b = b /= 0 ==> a `mod` b == fromIntegral a `mod` fromIntegral b
quotW128 a b = b /= 0 ==> a `quot` b == fromIntegral a `quot` fromIntegral b

testW128 =
        [ T "subW128" subW128
        , T "addW128"  addW128
        , T "mulW128"  mulW128
        , T "divW128"  divW128
        , T "remW128" remW128
        , T "modW128" modW128
        , T "quotW128" quotW128
        ]
addI128, subI128, mulI128 :: Int128 -> Int128 -> Bool
addI128 a b =  a + b == (fromIntegral a + fromIntegral b)
subI128 a b = a - b == (fromIntegral a - fromIntegral b)
mulI128 a b = a * b == (fromIntegral a * fromIntegral b)

divI128,remI128 :: Int128 -> Int128 -> Property
divI128 a b = b /= 0 ==> a `div` b == fromIntegral a `div` fromIntegral b
remI128 a b = b /= 0 ==> a `rem` b == fromIntegral a `rem` fromIntegral b

testI128 =
        [ T "subI128" subI128
        , T "addI128"  addI128
        , T "mulI128"  mulI128
        , T "divI128"  divI128
        , T "remI128" remI128
        ]
runtest (T str p) = putStr ("Testing " ++ str ++ ":") >> quickCheck p

runTests = mapM_ runtest

main = runTests testW128 >> runTests testW256 >> runTests testI128 >> runTests testFP

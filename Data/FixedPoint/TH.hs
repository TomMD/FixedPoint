module Data.FixedPoint.TH 
    ( mkWord
    , mkInt
    , mkFixedPoint
    ) where

import Language.Haskell.TH
import Data.Maybe

-- |@$(mkWord X)@ Makes a type alias named @WordX@ for a word of @X@ bits.
-- Notice @X@ must be a multiple of 8, 'Data.Word.Word8' must be in scope,
-- 'Data.FixedPoint.BigWord' must be in scope, and this splice will add
-- all smaller @WordY@ type aliases needed that aren't already in scope.
mkWord :: Int -> DecsQ
mkWord i
  | i `rem` 8 /= 0 = error ("Can not build a word of bit size " ++ show i)
  | otherwise = do
        info <- lookupTypeName (mkS i)
        let b = isNothing info
        if b then do
                let (h,l) = getParts i
                if h == 0
                    then do let l' = l`div`2
                            lD <- mkWord l'
                            a <- tySynD (mkW i) [] (appT (appT (conT $ mkName "BigWord") (conT $ mkW l')) (conT $ mkW l'))
                            return $ a:lD
                    else do hD <- mkWord h
                            lD <- mkWord l
                            a <- tySynD (mkW i) [] (appT (appT (conT $ mkName "BigWord") (conT $ mkW h)) (conT $ mkW l))
                            return $ a:(hD++lD)
             else return []

mkS :: Int -> String
mkS = ("Word" ++) . show

mkW,mkI :: Int -> Name
mkW = mkName . mkS

mkI = mkName . ("Int" ++) . show

getParts i =
    let l = 2^(floor (logBase 2 (fromIntegral i)))
        h = i - l
    in (h,l)

-- |@$(mkInt X)@ Makes a type alias named @IntX@ for an int of X bits.
-- See the requirements under 'mkWord' for additional information.
mkInt :: Int -> DecsQ
mkInt i = do
    info <- lookupTypeName (mkS i)
    if isNothing info
      then do
        d <- mkWord i
        e <- tySynD (mkName . ("Int" ++) . show $ i) [] (appT (conT $ mkName "BigInt") (conT $ mkW i))
        return (e:d)
      else return []

-- @mkFixedPoint X Y@ Builds a fixed point alias named @FixedPointX_Y@. See
-- the requirements under 'mkWord' for additional information.
mkFixedPoint :: Int -> Int -> DecsQ
mkFixedPoint int frac
  | (int + frac) `rem` 8 /= 0 = error "For fixed points, The sum of the integral and fractional bits must be a multiple of 8."
  | frac `rem` 8 /= 0 = error "For fixed points, the fractional representation must be a multiple of 8."
  | otherwise = do
      let flat = int + frac
      f <- mkInt flat
      i <- mkWord (flat*2)
      r <- mkWord frac
      x <- tySynD (mkName $ "FixedPoint" ++ show int ++ "_" ++ show frac)
                  [] (appT (appT (appT (conT $ mkName "GenericFixedPoint") (conT $ mkI flat)) (conT $ mkW $ flat*2)) (conT $ mkW frac))
      return (x : r ++ i ++ f)

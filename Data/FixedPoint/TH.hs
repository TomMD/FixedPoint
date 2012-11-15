module Data.FixedPoint.TH 
    ( mkWord
    ) where

import Language.Haskell.TH
import Data.Maybe

-- |@$(mkWord X)@ Makes a type alias named "WordX" for a word of X bits.
-- Notice X must be a multiple of 8, Data.Word.Word8 must be in scope,
-- Data.FixedPoint.BigWord must be in scope, and this splice will add
-- all smaller WordY type aliases needed that aren't already in scope.
mkWord :: Int -> DecsQ
mkWord i
  | i `rem` 8 /= 0 = error ("Can not build a word of bit size " ++ show i)
  | otherwise = do
        info <- lookupTypeName (mkS i)
        reportError $ show (info,i)
        let b = isNothing info
        if b then do
                let (h,l) = getParts i
                hD <- mkWord h
                lD <- mkWord l
                a <- tySynD (mkW i) [] (appT (appT (conT $ mkName "BigWord") (conT $ mkW h)) (conT $ mkW l))
                return $ a:(hD++lD)
             else return []
 where
  mkW = mkName . mkS
  mkS = ("Word" ++) . show

getParts i =
    let l = (floor (logBase 2 (fromIntegral i))^2)
        h = i - l
    in (h,l)

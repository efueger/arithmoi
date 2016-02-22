-- |
-- Module:      Math.NumberTheory.ModuliTests
-- Copyright:   (c) 2016 Andrew Lelechenko
-- Licence:     MIT
-- Maintainer:  Andrew Lelechenko <andrew.lelechenko@gmail.com>
-- Stability:   Provisional
--
-- Tests for Math.NumberTheory.Moduli
--

{-# LANGUAGE CPP          #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -fno-warn-type-defaults #-}

module Math.NumberTheory.ModuliTests
  ( testSuite
  ) where

import Test.Tasty

import Control.Arrow
import Data.Bits
import Data.List (tails)
#if MIN_VERSION_base(4,8,0)
#else
import Data.Word
#endif

import Debug.Trace

import Math.NumberTheory.Moduli
import Math.NumberTheory.TestUtils

toOdd :: Num a => a -> a
toOdd n = n * 2 + 1

jacobiProperty1 :: (Integral a, Bits a) => AnySign a -> NonNegative a -> Bool
jacobiProperty1 (AnySign a) (NonNegative (toOdd -> n)) = n == 1 && j == 1 || n > 1 && j == j'
  where
    j = jacobi a n
    j' = jacobi' a n

-- https://en.wikipedia.org/wiki/Jacobi_symbol#Properties, item 2
jacobiProperty2 :: (Integral a, Bits a) => AnySign a -> NonNegative a -> Bool
jacobiProperty2 (AnySign a) (NonNegative (toOdd -> n)) = jacobi a n == jacobi (a + n) n

-- https://en.wikipedia.org/wiki/Jacobi_symbol#Properties, item 3
jacobiProperty3 :: (Integral a, Bits a) => AnySign a -> NonNegative a -> Bool
jacobiProperty3 (AnySign a) (NonNegative (toOdd -> n)) = j == 0 && g /= 1 || abs j == 1 && g == 1
  where
    j = jacobi a n
    g = gcd a n

-- https://en.wikipedia.org/wiki/Jacobi_symbol#Properties, item 4
jacobiProperty4 :: (Integral a, Bits a) => AnySign a -> AnySign a -> NonNegative a -> Bool
jacobiProperty4 (AnySign a) (AnySign b) (NonNegative (toOdd -> n)) = jacobi (a * b) n == jacobi a n * jacobi b n

jacobiProperty4_Integer :: AnySign Integer -> AnySign Integer -> NonNegative Integer -> Bool
jacobiProperty4_Integer = jacobiProperty4

-- https://en.wikipedia.org/wiki/Jacobi_symbol#Properties, item 5
jacobiProperty5 :: (Integral a, Bits a) => AnySign a -> NonNegative a -> NonNegative a -> Bool
jacobiProperty5 (AnySign a) (NonNegative (toOdd -> m)) (NonNegative (toOdd -> n)) = jacobi a (m * n) == jacobi a m * jacobi a n

jacobiProperty5_Integer :: AnySign Integer -> NonNegative Integer -> NonNegative Integer -> Bool
jacobiProperty5_Integer = jacobiProperty5

-- https://en.wikipedia.org/wiki/Jacobi_symbol#Properties, item 6
jacobiProperty6 :: (Integral a, Bits a) => NonNegative a -> NonNegative a -> Bool
jacobiProperty6 (NonNegative (toOdd -> m)) (NonNegative (toOdd -> n)) = gcd m n /= 1 || jacobi m n * jacobi n m == (if m `mod` 4 == 1 || n `mod` 4 == 1 then 1 else -1)

invertModProperty :: AnySign Integer -> Positive Integer -> Bool
invertModProperty (AnySign k) (Positive m) = case invertMod k m of
  Nothing  -> k `mod` m == 0 || gcd k m > 1
  Just inv -> gcd k m == 1
      && k * inv `mod` m == 1 && 0 <= inv && inv < m

powerModProperty1 :: (Integral a, Bits a) => AnySign a -> AnySign Integer -> Positive Integer -> Bool
powerModProperty1 (AnySign e) (AnySign b) (Positive m)
  =  e < 0 && invertMod b m == Nothing
  || (0 <= pm && pm < m)
  where
    pm = powerMod b e m

powerModProperty2 :: (Integral a, Bits a) => AnySign a -> AnySign Integer -> AnySign Integer -> Positive Integer -> Bool
powerModProperty2 (AnySign e) (AnySign b1) (AnySign b2) (Positive m)
  =  e < 0 && (invertMod b1 m == Nothing || invertMod b2 m == Nothing)
  || pm1 * pm2 `mod` m == pm12
  where
    pm1  = powerMod b1  e m
    pm2  = powerMod b2  e m
    pm12 = powerMod (b1 * b2) e m

powerModProperty3 :: (Integral a, Bits a) => AnySign a -> AnySign a -> AnySign Integer -> Positive Integer -> Bool
powerModProperty3 (AnySign e1) (AnySign e2) (AnySign b) (Positive m)
  =  (e1 < 0 || e2 < 0) && invertMod b m == Nothing
  || pm1 * pm2 `mod` m == pm12
  where
    pm1  = powerMod b e1 m
    pm2  = powerMod b e2 m
    pm12 = powerMod b (e1 + e2) m

powerModProperty1_Integer :: AnySign Integer -> AnySign Integer -> Positive Integer -> Bool
powerModProperty1_Integer = powerModProperty1

powerModProperty2_Integer :: AnySign Integer -> AnySign Integer -> AnySign Integer -> Positive Integer -> Bool
powerModProperty2_Integer = powerModProperty2

powerModProperty3_Integer :: AnySign Integer -> AnySign Integer -> AnySign Integer -> Positive Integer -> Bool
powerModProperty3_Integer = powerModProperty3

powerMod'Property :: (Integral a, Bits a) => Positive a -> Positive Integer -> Positive Integer -> Bool
powerMod'Property (Positive e) (Positive b) (Positive m) = m == 1 || powerMod' b e m == powerMod b e m

powerMod'Property_Integer :: Positive Integer -> Positive Integer -> Positive Integer -> Bool
powerMod'Property_Integer = powerMod'Property

chineseRemainderProperty :: [(Integer, Positive Integer)] -> Bool
chineseRemainderProperty rms' = case chineseRemainder rms of
  Nothing -> not areCoprime
  Just n  -> areCoprime && map (n `mod`) ms == zipWith mod rs ms
  where
    rms = map (second getPositive) rms'
    (rs, ms) = unzip rms
    areCoprime = all (== 1) [ gcd m1 m2 | (m1 : m2s) <- tails ms, m2 <- m2s ]

sqrtModPProperty :: AnySign Integer -> Prime -> Bool
sqrtModPProperty (AnySign n) (Prime p) = case sqrtModP n p of
  Nothing -> jacobi n p == -1
  Just rt -> (p == 2 || jacobi n p /= -1) && rt ^ 2 `mod` p == n `mod` p

sqrtModPListProperty :: AnySign Integer -> Prime -> Bool
sqrtModPListProperty (AnySign n) (Prime p) = all (\rt -> rt ^ 2 `mod` p == n `mod` p) (sqrtModPList n p)

sqrtModP'Property :: Positive Integer -> Prime -> Bool
sqrtModP'Property (Positive n) (Prime p) = (p /= 2 && jacobi n p /= 1) || rt ^ 2 `mod` p == n `mod` p
  where
    rt = sqrtModP' n p

tonelliShanksProperty :: Positive Integer -> Prime -> Bool
tonelliShanksProperty (Positive n) (Prime p) = p `mod` 4 /= 1 || jacobi n p /= 1 || rt ^ 2 `mod` p == n `mod` p
  where
    rt = tonelliShanks n p

sqrtModPPProperty :: AnySign Integer -> (Prime, Power Int) -> Bool
sqrtModPPProperty (AnySign n) (Prime p, Power e) = gcd n p > 1 || case sqrtModPP n (p, e) of
  Nothing -> True
  Just rt -> rt ^ 2 `mod` (p ^ e) == n `mod` (p ^ e)

sqrtModPPListProperty :: AnySign Integer -> (Prime, Power Int) -> Bool
sqrtModPPListProperty (AnySign n) (Prime p, Power e) = gcd n p > 1 || (\rt -> rt ^ 2 `mod` (p ^ e) == n `mod` (p ^ e)) (sqrtModPPList n (p, e))

testSuite :: TestTree
testSuite = testGroup "Moduli"
  [ testGroup "jacobi"
    [ testSameIntegralProperty "matches jacobi'"              jacobiProperty1
    , testSameIntegralProperty "same modulo n"                jacobiProperty2
    , testSameIntegralProperty "consistent with gcd"          jacobiProperty3
    , testSmallAndQuick        "multiplicative 1"             jacobiProperty4_Integer
    , testSmallAndQuick        "multiplicative 2"             jacobiProperty5_Integer
    , testSameIntegralProperty "law of quadratic reciprocity" jacobiProperty6
    ]
  , testSmallAndQuick "invertMod" invertModProperty
  , testGroup "powerMod"
    [ testGroup "generic"
      [ testIntegralProperty "bounded between 0 and m" powerModProperty1
      , testIntegralProperty "multiplicative by base" powerModProperty2
      , testSameIntegralProperty "additive by exponent" powerModProperty3
      , testIntegralProperty "matches powerMod'" powerMod'Property
      ]
    , testGroup "Integer"
      [ testSmallAndQuick "bounded between 0 and m" powerModProperty1_Integer
      , testSmallAndQuick "multiplicative by base" powerModProperty2_Integer
      , testSmallAndQuick "additive by exponent" powerModProperty3_Integer
      , testSmallAndQuick "matches powerMod'" powerMod'Property_Integer
      ]
    ]
    , testSmallAndQuick "chineseRemainder" chineseRemainderProperty
    , testGroup "sqrtMod"
      [ testSmallAndQuick "sqrtModP" sqrtModPProperty
      , testSmallAndQuick "sqrtModPList" sqrtModPListProperty
      , testSmallAndQuick "sqrtModP'" sqrtModP'Property
      , testSmallAndQuick "tonelliShanks" tonelliShanksProperty
      , testSmallAndQuick "sqrtModPP" sqrtModPPProperty
      , testSmallAndQuick "sqrtModPPList" sqrtModPPListProperty
      ]
  ]

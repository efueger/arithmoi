-- |
-- Module:      Math.NumberTheory.Primes.SieveTests
-- Copyright:   (c) 2016 Andrew Lelechenko
-- Licence:     MIT
-- Maintainer:  Andrew Lelechenko <andrew.lelechenko@gmail.com>
-- Stability:   Provisional
--
-- Tests for Math.NumberTheory.Primes.Sieve
--

{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -fno-warn-type-defaults #-}

module Math.NumberTheory.Primes.SieveTests
  ( testSuite
  ) where

import Prelude hiding (words)

import Test.Tasty
import Test.Tasty.HUnit

#if MIN_VERSION_base(4,8,0)
#else
import Data.Word
#endif

import Math.NumberTheory.Primes.Sieve
import qualified Math.NumberTheory.Primes.Heap as H
import Math.NumberTheory.TestUtils

primesProperty1 :: Assertion
primesProperty1 = do
  assertEqual "Sieve == Heap" (trim primes) (trim H.primes)
  where
    trim = take 100000

sieveFromProperty1 :: AnySign Integer -> Bool
sieveFromProperty1 (AnySign lowBound)
  = trim (sieveFrom lowBound) == trim (H.sieveFrom lowBound)
  where
    trim = take 1000

primeSieveProperty1 :: AnySign Integer -> Bool
primeSieveProperty1 (AnySign highBound)
  = primeList (primeSieve highBound) == takeWhile (<= (highBound `max` 7)) primes

psieveListProperty1 :: Assertion
psieveListProperty1 = do
  assertEqual "primes == primeList . psieveList" (trim primes) (trim $ concatMap primeList psieveList)
  where
    trim = take 100000

psieveFromProperty1 :: AnySign Integer -> Bool
psieveFromProperty1 (AnySign lowBound)
  = trim (sieveFrom lowBound) == trim (filter (>= lowBound) (concatMap primeList $ psieveFrom lowBound))
  where
    trim = take 1000


testSuite :: TestTree
testSuite = testGroup "Sieve"
  [ testCase          "primes"     primesProperty1
  , testSmallAndQuick "sieveFrom"  sieveFromProperty1
  , testSmallAndQuick "primeSieve" primeSieveProperty1
  , testCase          "psieveList" psieveListProperty1
  , testSmallAndQuick "psieveFrom" psieveFromProperty1
  ]

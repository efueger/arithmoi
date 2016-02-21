-- |
-- Module:      Math.NumberTheory.Primes
-- Copyright:   (c) 2011 Daniel Fischer, 2016 Andrew Lelechenko
-- Licence:     MIT
-- Maintainer:  Andrew Lelechenko <andrew.lelechenko@gmail.com>
-- Stability:   Provisional
-- Portability: Non-portable (GHC extensions)
--

{-# LANGUAGE LambdaCase #-}

module Math.NumberTheory.Primes
  ( module P
  , Prime()
  , unPrime
  , nextPrime
  , precPrime
  ) where

import Math.NumberTheory.Primes.Sieve         as P
import Math.NumberTheory.Primes.Counting      as P
import Math.NumberTheory.Primes.Testing       as P hiding (FactorSieve)
import Math.NumberTheory.Primes.Factorisation as P

import Math.NumberTheory.Primes.Sieve.Eratosthenes (sieveRange)
import Math.NumberTheory.Primes.Sieve.Indexing (toPrim, toIdx)

import Data.Coerce

-- | Newtype to represent prime integers. It switches between different prime generators under the hood.
--   Use 'succ' \/ 'pred' to generate next \/ previous prime. Use @[n..m]@ syntax to get all primes between
--   given bounds. E. g.,
--
-- > [nextPrime 100 .. precPrime 200]
--
--   gives all primes between 100 and 200. You can also generate infinite prime sequences via @[n..]@.
newtype Prime = Prime {
  unPrime :: Integer -- ^ Unwrap prime.
  } deriving (Eq, Ord)

instance Show Prime where
  show = coerce (show :: Integer -> String)

-- | @[n,n'..]@ and @[n,n'..m]@ syntax is prohibited, becuase it is non-sense for primes.
instance Enum Prime where
  toEnum   = coerce $ nthPrime . toEnum
  fromEnum = coerce $ fromEnum . primeCount

  succ = coerce (\case
    2 -> 3
    3 -> 5
    5 -> 7
    p -> head $ filter isPrime $ map toPrim [toIdx p + 1 ..]
    :: Integer -> Integer)

  pred = coerce (\case
    2 -> error "Enum.pred{Prime}: tried to take `pred' of 2"
    3 -> 2
    5 -> 3
    7 -> 5
    p -> head $ filter isPrime $ map toPrim [toIdx p - 1, toIdx p - 2 ..]
    :: Integer -> Integer
    )

  -- 'dropWhile' is important, because 'psieveFrom' can actually contain primes less than p.
  enumFrom (Prime p) = coerce $ dropWhile (< p) $ concatMap primeList $ psieveFrom p

  enumFromTo (Prime p) (Prime q) = coerce $ takeWhile (<= q) $ dropWhile (< p) $
    -- For relatively close primes it is faster to use isPrime, than to build a sieve.
    if q - p < 20000 `min` truncate (fromInteger p ** 0.7 :: Double)
      then 2 : 3 : 5 : filter isPrime (map toPrim [toIdx p .. toIdx q])
      -- Is one segment of a sieve enough?
      else if q < toInteger sieveRange
        then           primeList $ primeSieve q
        else concatMap primeList $ psieveFrom p

  enumFromThen   _ = error "Enum.enumFromThen{Prime} is non-sense"
  enumFromThenTo _ = error "Enum.enumFromThenTo{Prime} is non-sense"

-- | Smallest prime, greater or equal to argument.
--
-- > nextPrime (-100) == Prime    2
-- > nextPrime  1000  == Prime 1009
-- > nextPrime  1009  == Prime 1009
nextPrime :: Integer -> Prime
nextPrime n
  | n <= 2    = Prime 2
  | n <= 3    = Prime 3
  | n <= 5    = Prime 5
  | otherwise = Prime $ head $ filter isPrime $
                  dropWhile (< n) $ map toPrim [toIdx n ..]
                  -- dropWhile is important, because toPrim (toIdx n) may appear to be < n.
                  -- E. g., toPrim (toIdx 99) == 97

-- | Largest prime, less or equal to argument. Undefined, when argument < 2.
--
-- > precPrime 100 == Prime 97
-- > precPrime  97 == Prime 97
precPrime :: Integer -> Prime
precPrime n
  | n < 2     = error $ "precPrime: tried to take `precPrime` of " ++ show n
  | n < 3     = Prime 2
  | n < 5     = Prime 3
  | n < 7     = Prime 5
  | otherwise = Prime $ head $ filter isPrime $
                  dropWhile (> n) $ map toPrim [toIdx n, toIdx n - 1 ..]
                  -- dropWhile is important, because toPrim (toIdx n) may appear to be > n.
                  -- E. g., toPrim (toIdx 100) == 101

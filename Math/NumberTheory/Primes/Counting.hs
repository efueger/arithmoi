-- |
-- Module:      Math.NumberTheory.Primes.Counting
-- Copyright:   (c) 2011 Daniel Fischer
-- Licence:     MIT
-- Maintainer:  Daniel Fischer <daniel.is.fischer@googlemail.com>
-- Stability:   Provisional
-- Portability: non-portable
--
-- Number of primes not exceeding @n@, @&#960;(n)@, and @n@-th prime; also fast, but
-- reasonably accurate approximations to these.
module Math.NumberTheory.Primes.Counting
    ( -- * Exact functions
      primeCount
    , nthPrime
      -- * Approximations
    , approxPrimeCount
    , nthPrimeApprox
    ) where

import Math.NumberTheory.Primes.Counting.Impl
import Math.NumberTheory.Primes.Counting.Approximate

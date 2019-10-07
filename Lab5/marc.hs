module Lab5 where

import Data.List
import System.Random
import Lecture5
import Test.QuickCheck
import System.Clock
import Control.Exception
import Formatting
import Formatting.Clock
import Test.QuickCheck.Monadic
import Control.Monad
import Data.Monoid

-- =============================================================================
-- EXERCISE 1
-- =============================================================================
-- RESULTS


-- =============================================================================
-- IMPLEMENTATION


-- (4 ^ 33) mod 5 can be computed by => (4 ^ 32) mod 5 * 4 mod 5
-- (4 ^ 32) mod 5 can be written to (rem 4 5) -> (rem (4 ^ 2) 5) -> (rem (4 ^ 4) 5) -> (rem (4 ^ 8) 5) -> (rem (4 ^ 16) 5) -> (rem (4 ^ 16) 32)

-- This is based on the below properties

-- Property 1:
-- rem (x ^ n ) m = rem ((rem x m) * (rem n * m)) m

-- if b is even:
-- (a ^ b) % c = ((a ^ b/2) * (a ^ b/2))%c ? this suggests divide and conquer
-- if b is odd:
-- (a ^ b) % c = (a * (a ^( b-1))%c

-- implementation at Lecture5.hs

testComparison :: Integer -> Integer -> Integer -> Property
testComparison base expo modulo =
  (modulo /= 0) && (expo >= 0) ==>
    exM base expo modulo == expM base expo modulo

-- Source : https://chrisdone.com/posts/measuring-duration-in-haskell/
excerciseOne = do
  let base = 50
  let expo = 100
  let modulo = 13

  start <- getTime Monotonic
  evaluate $ exM base expo modulo
  end <- getTime Monotonic
  putStrLn (show ((toNanoSecs (end - start))))
  startOne <- getTime Monotonic
  evaluate $ expM base expo modulo
  endOne <- getTime Monotonic
  putStrLn (show ((toNanoSecs (endOne - startOne))))
  -- start <- getTime Monotonic
  -- run (evaluate $ exM base expo modulo)
  -- end <- getTime Monotonic
  -- putStrLn (show end)


-- =============================================================================
-- TIME SPENT ~ 6 hours
-- =============================================================================


-- =============================================================================
-- EXERCISE 3
-- =============================================================================
-- RESULTS

-- =============================================================================
-- IMPLEMENTATION
-- See Lecture5.hs file
-- Implementation is under composites :: [Integer]
-- =============================================================================

-- =============================================================================
-- TIME SPENT 30 mins
-- =============================================================================


-- =============================================================================
-- EXERCISE 3
-- =============================================================================
-- RESULTS


-- =============================================================================
-- IMPLEMENTATION

-- Use the list of composite numbers to test Fermat's primality check.
-- What is the least composite number that you can find that fools the check, f
-- or prime_tests_F k with k=1,2,3 ? What happens if you increase k?

-- We make use of the list of composite prime numbers, this means that the numbers
-- in this list are not prime but are made by composition of primes, e.g.
-- the first 10 numbers are: [4,6,8,9,10,12,14,15,16,18]
-- These numbers are not prime, but we need to check if they pass the fermats
-- prime number test

-- K is the amount of times that we will repeat the fermat test
-- With a given k it will do the fermat primality check k times with a radom
-- number between 1 ≤ a < p and check a^p-1 ≡ 1 mod p
-- The function will return the first number in the list that will pass the
-- check

-- Limitations:
-- An ideal function would filter the whole list, but we could not figure that
-- out, because we where working with monats
getFirstFermatPrime :: [Integer] -> Int -> IO Integer
getFirstFermatPrime (x:xs) k = do
  -- for a given k, check if it passes the tests, which implies it is prime
  -- by the fermats check
  prime <- primeTestsF k x

  if prime then
    return x
  else
    -- Find a number that passes the test
    getFirstFermatPrime xs k

-- This function is really naive in its implementation
-- We give it a k and say repeat a 100 times finding a prime with
-- fermats check
minimumFalsePositiveComposite :: Int -> IO Integer
minimumFalsePositiveComposite k = do
  -- Build the list of false positives by running the function getFirstFermatPrime
  -- 100 times, we basicly hope that it will find new false postives
  x <- sequence [getFirstFermatPrime composites k | x <- [1..100]]
  -- Return the minimum false positve
  return (minimum x)

exerciseThree = do
    putStrLn "Minimum composite false positive by trying fermats"
    putStrLn "check 1 (k = 1) time for every number in the list of composites [1..100]:"
    resultOne <- minimumFalsePositiveComposite 1
    putStrLn "Minimum composite false positive by trying fermats"
    putStrLn "check 2 (k = 2) times for every number in the list of composites [1..100]:"
    resultTwo <- minimumFalsePositiveComposite 2
    putStrLn $ "Minumum : " ++ show resultTwo
    putStrLn "Minimum composite false positive by trying fermats"
    putStrLn "check 2 (k = 2) times for every number in the list of composites [1..100]:"
    resultThree <- minimumFalsePositiveComposite 3
    putStrLn $ "Minumum : " ++ show resultThree

-- =============================================================================

-- =============================================================================
-- TIME SPENT ~ 4 hours
-- =============================================================================



-- =============================================================================
-- EXERCISE 4
-- =============================================================================
-- RESULTS

-- =============================================================================
-- IMPLEMENTATION

-- In number theory, a Carmichael number is a composite number n which satisfies
-- the modular arithmetic congruence relation:
-- b ^ (n − 1) ≡ 1 ( mod n ) for all integers b which are relatively prime to n.

-- They are named for Robert Carmichael. The Carmichael numbers are the subset
-- K1 of the Knödel numbers.

-- Equivalently, a Carmichael number is a composite number n for which
-- b n ≡ b (mod n) for all integers b.

-- Fermat's primality check.
-- if p is prime, then for any integer a with 1 ≤ a < p, a^p-1 ≡ 1 mod p


carmichael :: [Integer]
carmichael = [ (6*k+1)*(12*k+1)*(18*k+1) |
       k <- [2..],
       prime (6*k+1),
       prime (12*k+1),
       prime (18*k+1) ]
--
-- testFermatPrimalityCheck :: Int -> Int -> IO [Integer]
-- testFermatPrimalityCheck n = filterM (primeTestsF k) (take n carmichael)


-- sequenceUntil :: (Monad m) => (a -> Bool) -> [m a] -> m [a]
-- sequenceUntil p xs = foldr (myLiftM2 (:) []) (return []) xs
--   where myLiftM2 f z m1 m2 = do
--             x1 <- m1
--             if p x1 then do x2 <- m2
--                             return $ f x1 x2
--                     else return z
--
-- printFirstFooled :: [Integer] -> IO [a] -> IO Integer
-- printFirstFooled comp ms = do
--     ys <- ms
--     return $ comp !! (length ys)
--
-- firstFool :: [Integer] -> Int -> IO Integer
-- firstFool comp k = printFirstFooled comp $ sequenceUntil (== False) $ map (primeTestsF k) comp
--
-- minFool' :: [Integer] -> Int -> Integer -> Int -> IO Integer
-- minFool' comp k x 0 = return x;
-- minFool' comp k x n = do
--     newX' <- newX
--     if newX' < x then
--         minFool' comp k newX' (n-1)
--     else
--         minFool' comp k x (n-1)
--     where newX = firstFool comp k
--
-- minFool :: [Integer] -> Int -> IO Integer
-- minFool comp k = do
--     x <- firstFool comp k
--     minFool' comp k x 100


-- =============================================================================
-- TIME SPENT ~ 30 min
-- =============================================================================

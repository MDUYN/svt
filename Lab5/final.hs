module Lab5 where

import Data.List
import System.Random
import Lecture5
import Test.QuickCheck
import Test.QuickCheck.Monadic
import System.Clock
import Control.Exception
import Control.Monad


-- =============================================================================
-- EXERCISE 1
-- =============================================================================
-- RESULTS

-- *Lab5> exerciseOne
-- 913975
-- 43850

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

-- exM  :: Integer -> Integer -> Integer -> Integer
-- exM base expo modules | expo == 0 = (rem 1 modules)
--                       | modules == 1 = 0
--                       | rem expo 2 == 1 = rem (rem ((rem base modules) * (exM base (expo - 1) modules)) modules) modules
--                       | otherwise = rem ((exM  base (div expo 2) modules) * (exM base (div expo  2) modules)) modules


testComparison :: Integer -> Integer -> Integer -> Property
testComparison base expo modulo =
  (modulo /= 0) && (expo >= 0) ==>
    exM base expo modulo == expM base expo modulo

-- Source : https://chrisdone.com/posts/measuring-duration-in-haskell/
exerciseOne = do
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

-- composites :: [Integer]
-- composites = filter (not . prime) [2..]

divisors :: Integer -> [Integer]
divisors n = [x | x <- [1..n], n `rem` x == 0]

-- Properties found at: https://en.wikipedia.org/wiki/Composite_number

-- Every positive integer is composite, prime, or the unit 1, so the composite numbers are exactly the numbers that are not prime and not a unit 1.
-- Composite numbers are always positive.
-- All composite numbers have at least three divisors.
checkComposite :: Integer -> Bool
checkComposite n = (n /= 1) && (length (divisors n) > 2) && (n > 0)


-- check that if a number is not 1, has more than 3 divisors and is positive, then it is in composite list.
prop_Composite :: Integer -> Property
prop_Composite n =
    checkComposite n  ==>
      n `elem` composites

indexGenerator :: Gen Integer
indexGenerator = abs <$> (arbitrary :: Gen Integer) `suchThat` (\x -> x >= 0)

-- checks if an element from the composite list is not 1, has more than 3 divisors and is positive.
prop_Composite' :: Integer -> Bool
prop_Composite' n = checkComposite (composites !! (fromIntegral n :: Int))

primeGenerator :: Gen Integer
primeGenerator = abs <$> (arbitrary :: Gen Integer) `suchThat` (\x -> (prime x) && x > 0)

-- The squares of primes are always composite, because p^2 has the divisors: {1, p, p^2}.
prop_CompositePrime :: Integer -> Bool
prop_CompositePrime n = (n^2) `elem` composites

exerciseTwo = do
  print "Exercise 02"
  print "Test if positive numbers that are not 1 and have atleast 3 divisors are in composites list"
  quickCheck prop_Composite
  print "Test if a number that is in composite list then the number is not 1, is positive and has atleast three divisors"
  quickCheckResult $ forAll indexGenerator prop_Composite'
  print "Test if squares of primes are composites"
  quickCheckResult $ forAll primeGenerator prop_CompositePrime
-- =============================================================================

-- =============================================================================
-- TIME SPENT 2 hours
-- =============================================================================


-- =============================================================================
-- EXERCISE 3
-- =============================================================================
-- RESULTS

-- *Lab5> exerciseThree
-- First composite false positive by trying fermats check
-- check 1 (k = 1) time until we find the first false positive:
-- First false positive : 85
-- First composite false positive by trying fermats
-- check 2 (k = 2) times  until we find the first false positive:
-- First false positive : 451
-- First composite false positive by trying fermats
-- check 3 (k = 3) times until we find the first false positive:
-- First false positive : 65
-- Now doing fermats check 1 (k = 1) times by filter the list of
-- composites till the range of 200
-- Result: [39,63,65,70,201]
-- Now doing fermats check 2 (k = 2) times by filter the list of
-- composites till the range of 200
-- Result: []
-- Now doing fermats check 3 (k = 3) times by filter the list of
-- composites till the range of 200
-- Result: []
-- Minimum composite false positive by trying fermats
-- check 1 (k = 1) times until we find the first false positive
-- with comparing the outcomes of 3 time running the same function
-- Minimum: 9
-- Minimum composite false positive by trying fermats
-- check 2 (k = 2) times until we find the first false positive
-- with comparing the outcomes of 3 time running the same function
-- Minimum: 27
-- Minimum composite false positive by trying fermats
-- check 3 (k = 3) times until we find the first false positive
-- with comparing the outcomes of 3 time running the same function

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

getFirstFermatPrime :: Int -> [Integer] -> IO Integer
getFirstFermatPrime k (x:xs) = do
  -- for a given k, check if it passes the tests, which implies it is prime
  -- by the fermats check
  prime <- primeTestsF k x

  if prime then
    return x
  else
    -- Find a number that passes the test
    getFirstFermatPrime k xs

-- This is a filter function to show  it takes to find a
filterFalsePositive :: Int -> Int -> [Integer] -> IO [Integer]
filterFalsePositive k n list = filterM (primeTestsF k) (take n list)

-- This function is really naive in its implementation
-- We give it a k and say repeat a 100 times finding a prime with
-- fermats check
minimumFalsePositiveNTimes :: Int -> Int -> [Integer] -> IO Integer
minimumFalsePositiveNTimes k n list = do
  -- Build the list of false positives by running the function getFirstFermatPrime
  -- 100 times, we basicly hope that it will find new false postives
  x <- sequence [getFirstFermatPrime k list | x <- [1..n]]
  -- Return the minimum false positve
  return (minimum x)

compGen :: Gen Integer
compGen =
  elements (take 50000 composites)


prop_factor :: Int -> Integer -> Property
prop_factor k n = monadicIO $ do
  value <- run (primeTestsF k n)

  Test.QuickCheck.Monadic.assert (not value)

exerciseThree = do

    print "Exercise 03"
    print "Test Fermat's primality check with (k=1)"
    quickCheckWith stdArgs { maxSuccess = 500000 } (forAll compGen (prop_factor 1))
    print "Test Fermat's primality check with (k=2)"
    quickCheckWith stdArgs { maxSuccess = 500000 } (forAll compGen (prop_factor 2))
    print "Test Fermat's primality check with (k=3)"
    quickCheckWith stdArgs { maxSuccess = 500000 } (forAll compGen (prop_factor 3))

    putStrLn "First composite false positive by trying fermats check "
    putStrLn "check 1 (k = 1) time until we find the first false positive: "
    resultOne <- getFirstFermatPrime 1 composites
    putStrLn ("First false positive : " ++ show resultOne)
    putStrLn "First composite false positive by trying fermats"
    putStrLn "check 2 (k = 2) times  until we find the first false positive: "
    resultTwo <- getFirstFermatPrime 2 composites
    putStrLn ("First false positive : " ++ show resultTwo)
    putStrLn "First composite false positive by trying fermats"
    putStrLn "check 3 (k = 3) times until we find the first false positive: "
    resultThree <- getFirstFermatPrime 3 composites
    putStrLn ("First false positive : " ++ show resultThree)
    putStrLn "Now doing fermats check 1 (k = 1) times by filter the list of "
    putStrLn "composites till the range of 200"
    resultListOne <- filterFalsePositive 1 200 composites
    putStrLn ("Result: " ++ show resultListOne)
    putStrLn "Now doing fermats check 2 (k = 2) times by filter the list of "
    putStrLn "composites till the range of 200"
    resultListTwo <- filterFalsePositive 2 200 composites
    putStrLn ("Result: " ++ show resultListTwo)
    putStrLn "Now doing fermats check 3 (k = 3) times by filter the list of "
    putStrLn "composites till the range of 200"
    resultListThree <- filterFalsePositive 3 200 composites
    putStrLn ("Result: " ++ show resultListThree)
    putStrLn "Minimum composite false positive by trying fermats"
    putStrLn "check 1 (k = 1) times until we find the first false positive "
    putStrLn "with comparing the outcomes of 3 time running the same function"
    resultMinimumOne <- minimumFalsePositiveNTimes 1 3 composites
    putStrLn ("Minimum: " ++ show resultMinimumOne)
    putStrLn "Minimum composite false positive by trying fermats"
    putStrLn "check 2 (k = 2) times until we find the first false positive "
    putStrLn "with comparing the outcomes of 3 time running the same function"
    resultMinimumTwo <- minimumFalsePositiveNTimes 2 3 composites
    putStrLn ("Minimum: " ++ show resultMinimumTwo)
    putStrLn "Minimum composite false positive by trying fermats"
    putStrLn "check 3 (k = 3) times until we find the first false positive "
    putStrLn "with comparing the outcomes of 3 time running the same function"
    resultMinimumThree <- minimumFalsePositiveNTimes 3 3 composites
    putStrLn ("Minimum: " ++ show resultMinimumThree)
-- =============================================================================

-- =============================================================================
-- TIME SPENT ~ 5 hours
-- =============================================================================


-- =============================================================================
-- EXERCISE 4
-- =============================================================================
-- RESULTS

-- *Lab5> exerciseFour
-- Minimum composite false positive by trying fermats
-- check 1 (k = 1) time until we find the first false positive
-- with comparing the outcomes of 3 time running the same function
-- Minimum: 294409
-- Minimum composite false positive by trying fermats
-- check 2 (k = 2) times until we find the first false positive
-- with comparing the outcomes of 2 time running the same function
-- Minimum: 294409
-- Minimum composite false positive by trying fermats
-- check 3 (k = 3) times until we find the first false positive
-- with comparing the outcomes of 3 time running the same function
-- Minimum: 294409

-- =============================================================================
-- IMPLEMENTATION

-- Use the list generated by the carmichael function for a further test of
-- Fermat's primality check.

-- In theory, a Carmichael number is a composite number n which satisfies
-- the modular arithmetic congruence relation: b ^ (n − 1) ≡ 1 ( mod n )
-- for all integers b which are relatively prime to n.

-- Also, a Carmichael number is a composite number n for which
-- b n ≡ b (mod n) for all integers b.

-- Fermat's primality check.
-- if p is prime, then for any integer a with 1 ≤ a < p, a^p-1 ≡ 1 mod p


carmichael :: [Integer]
carmichael = [ (6*k+1)*(12*k+1)*(18*k+1) |
       k <- [2..],
       prime (6*k+1),
       prime (12*k+1),
       prime (18*k+1) ]

getFirstMRPrime :: Int -> [Integer] -> IO Integer
getFirstMRPrime k (x:xs) = do
   -- for a given k, check if it passes the tests, which implies it is prime
   -- by the fermats check
  prime <- primeMR k x

  if prime then
    return x
  else
    -- Find a number that passes the test
    getFirstMRPrime k xs

-- Carmichael numbers that are false positves for fermats check are very large
-- I get most of the time 294409

-- Carmichael numbers that are false positves for MR check are very large
-- So large that I can't finish the test, see the output

exerciseFour = do
  putStrLn "Minimum carmichael false positive by trying fermats"
  putStrLn "check 1 (k = 1) time until we find the first false positive "
  putStrLn "with comparing the outcomes of 3 time running the same function"
  resultMinimumThree <- minimumFalsePositiveNTimes 1 3 carmichael
  putStrLn ("Minimum: " ++ show resultMinimumThree)
  putStrLn "Minimum carmichael false positive by trying fermats"
  putStrLn "check 2 (k = 2) times until we find the first false positive "
  putStrLn "with comparing the outcomes of 2 time running the same function"
  resultMinimumThree <- minimumFalsePositiveNTimes 2 3 carmichael
  putStrLn ("Minimum: " ++ show resultMinimumThree)
  putStrLn "Minimum carmichael false positive by trying fermats"
  putStrLn "check 3 (k = 3) times until we find the first false positive "
  putStrLn "with comparing the outcomes of 3 time running the same function"
  resultMinimumThree <- minimumFalsePositiveNTimes 3 3 carmichael
  putStrLn ("Minimum: " ++ show resultMinimumThree)
  putStrLn "First carmichael false positive by trying Miller-Rabin primality check"
  result <- getFirstMRPrime 1 carmichael
  putStrLn ("First result: " ++ show result)


-- =============================================================================
-- TIME SPENT ~ 30 min
-- =============================================================================


-- =============================================================================
-- EXERCISE 5
-- =============================================================================
-- RESULTS

-- "Miller-Rabin primality test (k=5), input composites"
-- +++ OK, passed 100 tests.
-- "if x^2-1 is prime, then x should be prime"
-- +++ OK, passed 100 tests.
-- "for p > 6: M(p) mod(6) =1 and mod(12) = 7 and mod(24) = 7 and mod(48) = 31 and mod(96) = 31"
-- +++ OK, passed 100 tests; 22 discarded.
-- *Lab5> ex

-- =============================================================================

genComp2 :: Gen Integer
genComp2 =
  elements (take 11 composites)

-- if primeMR k n is true, n is prime and 2^n-1 is prime.
prop_mr :: Integer -> Property
prop_mr n = monadicIO $ do
  value <- run (implementationCheck n)

  Test.QuickCheck.Monadic.assert(if value == True then (prime n && prime ((2 ^n )-1)) else True)

-- The first thing we notice is that they are always odd numbers when p>6:
--  M(p) mod(6) =1
--  M(p) mod(12) =7
--  M(p) mod(24) =7
--  M(p) mod(48) =31
--  M(p) mod(96) =31

-- http://www2.mae.ufl.edu/~uhk/MERSENNE-REVISITED.pdf

-- for p > 6: M(p) mod(6) =1 and mod(12) = 7 and mod(24) = 7 and mod(48) = 31 and mod(96) = 31
prop_mr3 :: Integer -> Property
prop_mr3 n =
  n > 6 ==>
    monadicIO $ do
    value <- run (implementationCheck n)

    Test.QuickCheck.Monadic.assert(if value == True then ((((2 ^n )-1) `mod` 6) == 1) && ((((2 ^n )-1) `mod` 12) == 7) && ((((2 ^n )-1) `mod` 24) == 7) && ((((2 ^n )-1) `mod` 48) == 31) && ((((2 ^n )-1) `mod` 96) == 31) else True)

-- with K = 1 this test fails often at 4. thats why we set k to 5.
implementationCheck n = primeMR 5 ((2 ^n )-1)

exponentsMP :: [Integer] -> IO()
exponentsMP (x:xs) = do
  value <- implementationCheck x
  if (value == True)
    then do print ("exponent " ++ (show x))
            exponentsMP xs
    else exponentsMP xs

mersenneP :: [Integer] -> IO()
mersenneP (x:xs) = do
  value <- implementationCheck x
  if (value == True)
    then do print ("Mersenne primes " ++ (show (x^2-1)))
            mersenneP xs
    else mersenneP xs

-- if x^2-1 is prime, then x should be prime
prop_primen :: Integer -> Property
prop_primen  n =
    monadicIO $ do
    value <- run (implementationCheck n)

    Test.QuickCheck.Monadic.assert(if value then prime n else True)


-- the mersenneP generates infinetly and big numbers need complex computations which take a while, so we terminated it after a few primes.
-- Results:
-- "Mersenne primes 3"
-- "Mersenne primes 8"
-- "Mersenne primes 24"
-- "Mersenne primes 48"
-- "Mersenne primes 168"
-- "Mersenne primes 288"

-- There are an infinite amount of MERSENNE primes, but 51 have been identfied.
-- The largest known term is 2^82,589,933
--

exerciseFive = do
  print"Miller-Rabin primality test (k=5), input composites"
  quickCheckWith stdArgs { maxSuccess = 100 } $ forAll genComp2 (prop_mr)
  print"if x^2-1 is prime, then x should be prime"
  quickCheckWith stdArgs { maxSuccess = 100 } $ forAll genComp2 (prop_primen)
  print"for p > 6: M(p) mod(6) =1 and mod(12) = 7 and mod(24) = 7 and mod(48) = 31 and mod(96) = 31"
  quickCheckWith stdArgs { maxSuccess = 100 } $ forAll genComp2 (prop_mr3)

  -- Goes to infinite, uncomment to test:

  -- print"Generate Mersenne primes:"
  -- mersenneP primes
  -- print"Generate Mersenne primes:"
  -- exponentsMP primes

-- =============================================================================
-- TIME SPENT ~ 3 hours
-- =============================================================================

-- =============================================================================
-- EXERCISE 5
-- =============================================================================
-- RESULTS
-- =============================================================================

-- You can check that the number pairs (x,y) that occur in a tree n are precisely the pairs in the set {(x,y) | 1 ≤ x ≤ n, 1 ≤ y ≤ n with x, y co-prime}.
-- You can put all the number pairs (x,y) that occur in tree in a list. recursively loop through the list and for each tuple x, y we check
-- x `coprime'` y. If this holds for all nodes in the tree, we return True.

tree1 n = grow (step1 n) (1,1)
step1 n = \ (x,y) -> if x+y <= n then [(x+y,x),(x,x+y)] else [] -- step function

tree2 n = grow (step2 n) (1,1)
step2 n = \ (x,y) -> if x+y <= n then [(x+y,y),(x,x+y)] else [] -- step function

coprimeTree :: (Tree (Integer, Integer)) -> Bool
coprimeTree (T (x,y) []) = coprime' x y
coprimeTree (T (x,y) ts) = if coprime' x y then all coprimeTree ts else False

testTree1 :: Integer -> Property
testTree1 n =
  n > 0 ==>
   coprimeTree (tree1 n)

testTree2 :: Integer -> Property
testTree2 n =
 n > 0 ==>
  coprimeTree (tree2 n)

exerciseSix = do
  print"Tree 1 Test"
  quickCheck testTree1
  print"Tree 2 Test"
  quickCheck testTree2

-- =============================================================================
-- TIME SPENT ~ 3 hours
-- =============================================================================

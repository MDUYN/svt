import Data.List
import System.Random
import Lecture5
import Test.QuickCheck
import Test.QuickCheck.Monadic


-- Exercise 01

-- Exercise 02

composites :: [Integer]
composites = filter (not . prime) [2..]

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


-- Exercise 03

compGen :: Gen Integer
compGen =
  elements (take 50000 composites)

prop_factor :: Int -> Integer -> Property
prop_factor k n = monadicIO $ do
  value <- run (primeTestsF k n)

  assert (not value)

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
  x <- sequence [getFirstFermatPrime composites k | x <- take 100 composites]
  -- Return the minimum false positve
  return (minimum x)

exerciseThree = do
  print "Exercise 03"
  print "Test Fermat's primality check with (k=1)"
  quickCheckWith stdArgs { maxSuccess = 500000 } $ forAll compGen (prop_factor 1)
  print "Test Fermat's primality check with (k=2)"
  quickCheckWith stdArgs { maxSuccess = 500000 } $ forAll compGen (prop_factor 2)
  print "Test Fermat's primality check with (k=3)"
  quickCheckWith stdArgs { maxSuccess = 500000 } $ forAll compGen (prop_factor 3)

  putStrLn "Minimum composite false positive by trying fermats"
  putStrLn "check 1 (k = 1) time for every number in the list of composites [1..100]:"
  resultOne <- minimumFalsePositiveComposite 1
  putStrLn $ "Minumum : " ++ show resultOne
  putStrLn "Minimum composite false positive by trying fermats"
  putStrLn "check 2 (k = 2) times for every number in the list of composites [1..100]:"
  resultTwo <- minimumFalsePositiveComposite 2
  putStrLn $ "Minumum : " ++ show resultTwo
  putStrLn "Minimum composite false positive by trying fermats"
  putStrLn "check 2 (k = 2) times for every number in the list of composites [1..100]:"
  resultThree <- minimumFalsePositiveComposite 3
  putStrLn $ "Minumum : " ++ show resultThree


-- exercise 05

genComp2 :: Gen Integer
genComp2 =
  elements (take 11 composites)

-- if primeMR k n is true, n is prime and 2^n-1 is prime.
prop_mr :: Integer -> Property
prop_mr n = monadicIO $ do
  value <- run (implementationCheck n)

  assert(if value == True then (prime n && prime ((2 ^n )-1)) else True)


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

    assert(if value == True then ((((2 ^n )-1) `mod` 6) == 1) && ((((2 ^n )-1) `mod` 12) == 7) && ((((2 ^n )-1) `mod` 24) == 7) && ((((2 ^n )-1) `mod` 48) == 31) && ((((2 ^n )-1) `mod` 96) == 31) else True)

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

    assert(if value then prime n else True)


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


-- exercise 06

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

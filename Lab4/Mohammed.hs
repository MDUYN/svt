import Data.List
import Data.Char
import Test.QuickCheck
import Lecture4
import SetOrd
import Generators
import Debug.Trace
import System.Random
import Data.Tuple

-- Takes two sets, checks if an element from set1 is in set2.
-- If true, it adds it to the output set
-- If false, it checks next element of set1.
-- If all elements of set1 are checked, the output set contains all elements of set1 that were found in set2.
-- The output is the intersect of the two sets.
intersectSet :: (Eq a, Ord a) => Set a -> Set a -> Set a
intersectSet (Set []) set2 = Set []
intersectSet set1 (Set []) = Set []
intersectSet (Set (x:xs)) set2 =
  if (x `inSet` set2) then (insertSet x (intersectSet (Set xs) set2)) else intersectSet (Set xs) set2

-- Takes two sets, checks if element from set1 is in set2
-- if True, it checks next element of set1
-- if false, it adds it to the output set and checks next element of set1.
-- if all elements of set1 are consumed, the output set contains all elements from set1 that were not in set2.
-- the output set is the Difference of set1 on set2.
differenceSet :: (Eq a, Ord a) => Set a -> Set a -> Set a
differenceSet (Set []) set2 = (Set [])
differenceSet set1 (Set []) = set1
differenceSet (Set (x:xs)) set2 =
  if not (x `inSet` set2) then (insertSet x (differenceSet (Set xs) set2)) else differenceSet (Set xs) set2

-- the properties tested come from: https://www.mathstopia.net/sets/intersection-set

-- 1. Commutative Property: If A and B are two sets then, A∩B = B∩A
-- 2. Associative Property: If A, B and C are three sets then, A∩(B∩C)= (A∩B)∩C.
-- 3. Identity Property: The intersection of a set and the empty set is always the empty set,
--    i.e, A∩ϕ = ϕ.

-- If A and B are two sets then, A∩B = B∩A
commutativeProperty :: (Set Int -> Set Int -> Set Int) -> Set Int -> Set Int -> Bool
commutativeProperty f set1 set2 =
  (f set1 set2) == (f set2 set1)
-- quickCheck (commutativeProperty intersectSet)

-- If A, B and C are three sets then, A∩(B∩C)= (A∩B)∩C.
associativeProperty :: (Set Int -> Set Int -> Set Int) -> Set Int -> Set Int -> Set Int -> Bool
associativeProperty f set1 set2 set3 =
  (f (set1) (f set2 set3)) == (f (f set1 set2) (set3))
-- quickCheck (associativeProperty intersectSet)

--A∩ϕ = ϕ
identityProperty :: (Set Int -> Set Int -> Set Int) -> Set Int -> Bool
identityProperty f set1 =
  (f (set1) (Set []) ) == (Set [])
-- quickCheck (identityProperty intersectSet)

-- ϕ∩A = ϕ
identityProperty' :: (Set Int -> Set Int -> Set Int) -> Set Int -> Bool
identityProperty' f set1 =
  (f (Set []) (set1) ) == emptySet
-- quickCheck (identityProperty' intersectSet)


-- 1. If set A and B are equal then, A-B = A-A =  ϕ (empty set)
-- 2. When an empty set is subtracted from a set (suppose set A) then,
--    result is that set itself, i.e, A - ϕ = A.
-- 3. When a set is subtracted from an empty set then, the result is an empty set, i.e,  ϕ - A =  ϕ.
-- 4. When a superset is subtracted from a subset, then result is an empty set, i.e, A - B =  ϕ if A ⊂ B
-- 5. If A and B are disjoint sets then, A-B = A and B-A = B

-- A-A = ϕ
diffSameSetTest :: Set Int -> Bool
diffSameSetTest set =
  differenceSet set set == emptySet
-- quickCheck (diffSameSetTest)

-- A - ϕ = A
diffEmptySetTest :: Set Int -> Bool
diffEmptySetTest set =
  differenceSet set emptySet == set
-- quickCheck (diffEmptySetTest)

-- ϕ - A = ϕ
diffEmptySetTest' :: Set Int -> Bool
diffEmptySetTest' set =
  differenceSet emptySet set == emptySet
-- quickCheck (diffEmptySetTest')

-- A - B =  ϕ if A ⊂ B
diffSuperSubSet' :: Int -> Set Int -> Bool
diffSuperSubSet' n set1 =
  -- trace ((show set1) ++ ", " ++ (show (takeSet n set1))) (
    differenceSet (takeSet n set1) set1 == emptySet
-- quickCheck (diffSuperSubSet')


-- 1. Commutative Property: If A and B are two sets then, A∪B = B∪A
-- 2. Associative Property: If A, B and C are three sets then, A∪(B∪C)= (A∪B)∪C
-- 3. Identity Property: The union of a set and the empty set it that set itself, i.e, A∪ϕ = A.

-- the functions are the same for union as for intersection. except the Identity Property.

-- To test the first two properties:
-- quickCheck (commutativeProperty unionSet)
-- quickCheck (associativeProperty unionSet)

--A∪ϕ = A
identityPropertyUnion :: (Set Int -> Set Int -> Set Int) -> Set Int -> Bool
identityPropertyUnion f set1 =
  (f (set1) (Set []) ) == set1
-- quickCheck (identityPropertyUnion unionSet)

-- ϕ∪A= A
identityPropertyUnion' :: (Set Int -> Set Int -> Set Int) -> Set Int -> Bool
identityPropertyUnion' f set1 =
  (f (Set []) (set1) ) == set1
-- quickCheck (identityPropertyUnion' unionSet)

-- This formula checks for each element in set1 whether it is found in set2.
-- It returns a list of booleans, one for each element of set1.
-- True means it is not found in set2
-- False means it is found
-- All True means the sets are disjoint.
disjoint :: Set Int -> Set Int -> [Bool]
disjoint (Set []) set2 = []
disjoint set1 (Set []) = []
disjoint (Set (x:xs)) set2 =
  (not (x `inSet` set2):disjoint (Set xs) set2)

-- Check if all the elements in list are True.
isDisjoint set1 set2 = all (==True) (disjoint set1 set2)

-- Tests:
-- Test commutativeProperty for intersectSet function
testPropertyCom :: Int -> IO ()
testPropertyCom n =
    if (n == 0) then (print "All 100 tests passed!")
    else do
      set1 <- setGenerator (1, 100) (1, 99999)
      set2 <- setGenerator (1, 100) (1, 99999)
      if (commutativeProperty intersectSet set1 set2) then (testPropertyCom (n-1))
      else error ("Test failed!")
-- testPropertyCom 100 (or more if you want)

-- Test commutativeProperty for unionSet function
testPropertyCom' :: Int -> IO ()
testPropertyCom' n =
    if (n == 0) then (print "All 100 tests passed!")
    else do
      set1 <- setGenerator (1, 100) (1, 99999)
      set2 <- setGenerator (1, 100) (1, 99999)
      if (commutativeProperty unionSet set1 set2) then (testPropertyCom' (n-1))
      else error ("Test failed!")
-- testPropertyCom' 100 (or more if you want)

-- Test associativeProperty for intersectSet function
testPropertyAss :: Int -> IO ()
testPropertyAss n =
    if (n == 0) then (print "All 100 tests passed!")
    else do
      set1 <- setGenerator (1, 100) (1, 99999)
      set2 <- setGenerator (1, 100) (1, 99999)
      set3 <- setGenerator (1, 100) (1, 99999)
      if (associativeProperty intersectSet set1 set2 set3) then (testPropertyAss (n-1))
      else error ("Test failed!")
-- testPropertyAss 100 (or more if you want)

-- Test associativeProperty for unionSet function
testPropertyAss' :: Int -> IO ()
testPropertyAss' n =
    if (n == 0) then (print "All 100 tests passed!")
    else do
      set1 <- setGenerator (1, 100) (1, 99999)
      set2 <- setGenerator (1, 100) (1, 99999)
      set3 <- setGenerator (1, 100) (1, 99999)
      if (associativeProperty unionSet set1 set2 set3) then (testPropertyAss' (n-1))
      else error ("Test failed!")
-- testPropertyAss' 100 (or more if you want)

-- Test identityProperty for intersectSet function
testPropertyId :: Int -> IO ()
testPropertyId n =
    if (n == 0) then (print "All 100 tests passed!")
    else do
      set1 <- setGenerator (1, 100) (1, 99999)
      if ((identityProperty intersectSet set1) && (identityProperty' intersectSet set1)) then (testPropertyId (n-1))
      else error ("Test failed!")
-- testPropertyId 100 (or more if you want)

-- Test identityProperty for unionSet function
testPropertyId' :: Int -> IO ()
testPropertyId' n =
    if (n == 0) then (print "All 100 tests passed!")
    else do
      set1 <- setGenerator (1, 100) (1, 99999)
      if ((identityPropertyUnion unionSet set1) && (identityPropertyUnion' unionSet set1)) then (testPropertyId' (n-1))
      else error ("Test failed!")
-- testPropertyId' 100 (or more if you want)


-- Test testDiffSame for differenceSet function
testDiffSame:: Int -> IO ()
testDiffSame n =
    if (n == 0) then (print "All 100 tests passed!")
    else do
      set1 <- setGenerator (1, 100) (1, 99999)
      if (diffSameSetTest set1) then (testDiffSame (n-1))
      else error ("Test failed!")
-- testDiffSame 100 (or more if you want)

-- Test testDiffEmpty for differenceSet function
testDiffEmpty:: Int -> IO ()
testDiffEmpty n =
    if (n == 0) then (print "All 100 tests passed!")
    else do
      set1 <- setGenerator (1, 100) (1, 99999)
      if ((diffEmptySetTest set1) && (diffEmptySetTest' set1)) then (testDiffEmpty (n-1))
      else error ("Test failed!")
-- testDiffEmpty 100 (or more if you want)

-- Test testDiffSub for differenceSet function
testDiffSub :: Int -> IO ()
testDiffSub n =
    if (n == 0) then (print "All 100 tests passed!")
    else do
      set1 <- setGenerator (1, 100) (1, 99999)
      if (diffSuperSubSet' 10 set1) then (testDiffSub (n-1))
      else error ("Test failed!")
-- testDiffSub 100 (or more if you want)

prop_Disjoint :: Set Int -> Set Int -> Property
prop_Disjoint set1 set2 =
    isDisjoint set1 set2 ==>
      ((differenceSet set1 set2 == set1) && (differenceSet set2 set1 == set2))

-- Test Disjoint for differenceSet function
testPropertyDisjoint:: Int -> IO ()
testPropertyDisjoint n =
    if (n == 0) then (print "All 100 tests passed!")
    else do
      set1 <- setGenerator (1, 100) (1, 500)
      set2 <- setGenerator (1, 100) (600, 1000)  -- Makes sure the sets are disjoint
      if ((differenceSet set1 set2 == set1) && (differenceSet set2 set1 == set2)) then (testPropertyCom (n-1))
      else error ("Test failed!")
-- testPropertyDisjoint 100 (or more if you want)

--------------------------
-- In total we have tested the following properties:
-- For Intersect & Union: Commutative Property, Associative Property & Identity Property
-- For Difference:
      -- 1. If set A and B are equal then, A-B = A-A =  ϕ (empty set)
      -- 2. When an empty set is subtracted from a set (suppose set A) then,
      --    result is that set itself, i.e, A - ϕ = A.
      -- 3. When a set is subtracted from an empty set then, the result is an empty set, i.e,  ϕ - A =  ϕ.
      -- 4. When a superset is subtracted from a subset, then result is an empty set, i.e, A - B =  ϕ if A ⊂ B
      -- 5. If A and B are disjoint sets then, A-B = A and B-A = B
-- All of the tests passed. The quickCheck version and the own generator versions of the tests are provided.
-- for the own generators i've generated sets which can contain the numbers 1 to 99999, with a maximum length of 100
-- all tests returned passed!
--------------------------

exerciseTwo = do
  print "Exercise 01"

  print "Intersection test:"
  print "Commutative Property:"
  quickCheck (commutativeProperty intersectSet)
  print "Associative Property:"
  quickCheck (associativeProperty intersectSet)
  print "Identity Property:"
  print "A `intersect` empty:"
  quickCheck (identityProperty intersectSet)
  print "empty `intersect` A:"
  quickCheck (identityProperty' intersectSet)

  print "Difference test:"
  print "A-A = Empty"
  quickCheck (diffSameSetTest)
  print "A - empty = A"
  quickCheck (diffEmptySetTest)
  print "empty - A = empty"
  quickCheck (diffEmptySetTest')
  print "A - B = empty, if A is a subset of B"
  quickCheck (diffSuperSubSet')
  print "A-B = A or B-A = B if A and B are Disjoint sets"
  quickCheck prop_Disjoint


  print "Union test:"
  print "Commutative Property:"
  quickCheck (commutativeProperty unionSet)
  print "Associative Property:"
  quickCheck (associativeProperty unionSet)
  print "Identity Property:"
  print "A `union` empty:"
  quickCheck (identityPropertyUnion unionSet)
  print "empty `union` A:"
  quickCheck (identityPropertyUnion' unionSet)



  print "Own Generated Tests: "

  print "Intersection test:"
  print "Commutative Property:"
  testPropertyCom 100
  print "Associative Property:"
  testPropertyAss 100
  print "Identity Property:"
  print "A `intersect` empty && empty `intersect` A:"
  testPropertyId 100

  print "Difference test:"
  print "A-A = Empty"
  testDiffSame 100
  print "A - empty = A && empty - A = empty"
  testDiffEmpty 100
  print "A - B = empty, if A is a subset of B"
  testDiffSub 100
  print "A-B = A or B-A = B if A and B are Disjoint sets"
  testPropertyDisjoint 100

  print "Union test:"
  print "Commutative Property:"
  testPropertyCom' 100
  print "Associative Property:"
  testPropertyAss' 100
  print "Identity Property:"
  print "A `union` empty && empty `union` A:"
  testPropertyId' 100


-- Time: 10 Hours.


-- Exercise 3

type Rel a = [(a,a)]

-- takes a set of Relations, "Loops" through it and consumes elements untill the input list is empty.
-- if the flipped element is already in the output set, we ignore it and check next element.
-- if the flipped element is not in the output set, add it to the output set, and check next element.
-- the output is a symetric closure of the input set.
symClos :: Ord a => Rel a -> Rel a
symClos [] = []
symClos total@((a,b):xs) = if not ((b,a) `elem` total) then sort (nub (((a,b):(b,a):(symClos xs)))) else (sort (nub (((a,b):symClos xs))))

-- Time: 45 minutes

-- Exercise 4

-- insertList :: a -> [a] -> [a]
-- insertList x [] = [x]
-- insertList x ys@(y:ys') = case compare x y of
--                                  GT -> y : insertList x ys'
--                                  EQ -> ys
--                                  _  -> x : ys

distinctElem :: (Eq a) => Rel a -> [a]
distinctElem [] = []
distinctElem total@((x,y):xs) = nub (y: distinctElem xs)

isSerial :: Eq a => [a] -> Rel a -> Bool
isSerial distElem [] = True
isSerial distElem total@((a,b):xs)= if a `elem` distElem then isSerial distElem xs else False


-- Exercise 5
infixr 5 @@
(@@) :: Eq a => Rel a -> Rel a -> Rel a
r @@ s =
 nub [ (x,z) | (x,y) <- r, (w,z) <- s, y == w ]

-- takes a set of Relations, "Loops" through it untill the @@ function has no effect on the set anymore.
-- trClos at stel x == trClos at step x+1
-- It returns the trasitive closure of a set using the @@ function provided.
trClos :: Ord a => Rel a -> Rel a
trClos xs
  | (xs == nextClos) = xs
  | otherwise = trClos (sort (nub (xs ++ (xs @@ xs))))
    where nextClos = sort (nub (xs ++ (xs @@ xs)))


-- Exercise 9 (Bonus Euler)


-- Problem 30 Euler
-- The upper and lowerbound of the brute Force algorithm is given here: https://www.xarg.org/puzzle/project-euler/problem-30/

-- Input of our function
inputList :: [Integer]
inputList = [10..355000]

-- Takes an Int, returns each digit in a list.
digits :: Integer -> [Integer]
digits n = map (\x -> read [x] :: Integer) (show n)

-- Takes the sum of all the digits to the power of 5
pow5 n = sum (map (^5) (digits n))

-- Goes through whole input list, returns sum of powers of 5 where int == digits ^5
fifthPow :: Integer
fifthPow = sum [if (x == pow5 x ) then x else 0 | x <- inputList]

exerciseNine = do
  fifthPow  -- Takes ~10 secs

-- =============================================================================
-- EXERSICE 6
-- =============================================================================
-- RESULTS
-- =============================================================================
-- IMPLEMENTATION
-- Test the functions symClos and trClos from the previous exercises.
-- Devise your own test method for this. Try to use random test generation.
-- Define reasonable properties to test. Can you use QuickCheck? How?

-- For every (x,y) ∈ A -> (y,x) ∈ A
checkSymmetry :: Ord a => Rel a -> Bool
-- Property: Get every pair for symmetry list and check if the swap of elements is in symmetry list
-- (x,y) => swap => (y,x)
checkSymmetry xs = and [elem (swap x) symmetry  | x <- symmetry]
  where symmetry = symClos xs

checkTransitivity :: Ord a => Rel a -> Bool
-- Property: Get every pair for transitive list and check if there is a pair (a,b) and a pair (c,d)
-- and b == d then there must be a pair (a, d) in the transitive list in order to let it be transitive
checkTransitivity xs = and [elem (a,d) transitive | (a,b) <- transitive, (c,d) <- transitive, b == c]
  where
    transitive = trClos xs

exerciseSix = do
    print "QuickCheck for symClos function"
    quickCheck (checkSymmetry :: Rel Int -> Bool)
    print "QuickCheck for trClos function"
    quickCheck (checkTransitivity :: Rel Int -> Bool)

import Generators
import SetOrd
import Data.Tuple
import Data.List
import Lecture4
import Test.QuickCheck

-- =============================================================================
-- EXERCISE 2
-- =============================================================================
-- RESULTS

-- *Main> exerciseTwo 
-- "Exercise 01"
-- "Intersection test:"
-- "Commutative Property:"
-- +++ OK, passed 100 tests.
-- "Associative Property:"
-- +++ OK, passed 100 tests.
-- "Identity Property:"
-- "A `intersect` empty:"
-- +++ OK, passed 100 tests.
-- "empty `intersect` A:"
-- +++ OK, passed 100 tests.
-- "Difference test:"
-- "A-A = Empty"
-- +++ OK, passed 100 tests.
-- "A - empty = A"
-- +++ OK, passed 100 tests.
-- "empty - A = empty"
-- +++ OK, passed 100 tests.
-- "A - B = empty, if A is a subset of B"
-- +++ OK, passed 100 tests.
-- "A-B = A or B-A = B if A and B are Disjoint sets"
-- +++ OK, passed 100 tests; 489 discarded.
-- "Union test:"
-- "Commutative Property:"
-- +++ OK, passed 100 tests.
-- "Associative Property:"
-- +++ OK, passed 100 tests.
-- "Identity Property:"
-- "A `union` empty:"
-- +++ OK, passed 100 tests.
-- "empty `union` A:"
-- +++ OK, passed 100 tests.
-- "Own Generated Tests: "
-- "Intersection test:"
-- "Commutative Property:"
-- "All 100 tests passed!"
-- "Associative Property:"
-- "All 100 tests passed!"
-- "Identity Property:"
-- "A `intersect` empty && empty `intersect` A:"
-- "All 100 tests passed!"
-- "Difference test:"
-- "A-A = Empty"
-- "All 100 tests passed!"
-- "A - empty = A && empty - A = empty"
-- "All 100 tests passed!"
-- "A - B = empty, if A is a subset of B"
-- "All 100 tests passed!"
-- "A-B = A or B-A = B if A and B are Disjoint sets"
-- "All 100 tests passed!"
-- "Union test:"
-- "Commutative Property:"
-- "All 100 tests passed!"
-- "Associative Property:"
-- "All 100 tests passed!"
-- "Identity Property:"
-- "A `union` empty && empty `union` A:"
-- "All 100 tests passed!"

-- =============================================================================
-- IMPLEMENTATION

-- Symmetric closure => symmetry:  ∀x(xRy ⇒ yRx)
-- if for all x, y ∈ A: if xRy then yRx.
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
-- =============================================================================
-- TIME SPENT ~ 10 hours
-- =============================================================================

-- =============================================================================
-- EXERCISE 3
-- =============================================================================
-- RESULTS

-- *Main> exerciseThree
-- Input [(1,2),(2,3),(3,4)]
-- Correct output [(1,2),(2,1),(2,3),(3,2),(3,4),(4,3)]
-- Result: [(1,2),(2,1),(2,3),(3,2),(3,4),(4,3)]

-- =============================================================================
-- IMPLEMENTATION

-- Symmetric closure => symmetry:  ∀x(xRy ⇒ yRx)
-- if for all x, y ∈ A: if xRy then yRx.

type Rel a = [(a,a)]

symClos :: Ord a => Rel a -> Rel a
-- Swap tuple and check if in list else add to new list
-- and concat with original list
symClos xs = sort (xs ++ sort[swap x | x <- xs, notElem (swap x) xs])

exerciseThree = do
  let exampleOne = [(1,2),(2,3),(3,4)]
  let resultOne = [(1,2),(2,1),(2,3),(3,2),(3,4),(4,3)]
  putStrLn $ "Input " ++ show exampleOne
  putStrLn $ "Correct output " ++ show resultOne
  putStrLn $ "Result: " ++ show (symClos exampleOne)
-- =============================================================================
-- TIME SPENT ~ 2 hour
-- =============================================================================


-- =============================================================================
-- EXERCISE 4
-- =============================================================================
-- RESULTS

-- *Main> exerciseFour
-- relation A: [(1,2),(2,3),(3,1)]
-- in domain: [1,2,3]
-- isSerial?: True
-- relation B: [(1,2),(2,3)]
-- in domain: [1,2,3]
-- isSerial?: False
-- relation B: [(1,2),(2,3),(3,1)]
-- in domain: [3,4,5,6]
-- isSerial?: False
-- *** Gave up! Passed only 0 tests; 1000 discarded tests.

-- =============================================================================
-- serial => Linear: ∀x(x ∈ A)∃(y ∈ A) -> xRy

-- if for all x ∈ A: if x ∈ A ∃ y ∈ A then xRy

-- Relations A = [(1,2), (2,3), (3,1)] in domain D = [1,2,3,4]
-- A is serial

-- Relations B = [(1,2), (2,3)] in domain D = [1,2,3,4]
-- B is not serial

-- Relations C = [(1,2), (2,3), (3,1)] in domain D = [3,4,5,6]
-- C is not serial
isSerial :: Eq a => [a] -> Rel a -> Bool
isSerial xs ys = not (null ys || null xs)
  && ((xs, ys, 0) $$
    fix (\ f (xs, ys, n) -> ((length ys == n) || (fstTupleElem (snd (ys !! n)) ys && elem (snd (ys !! n)) xs) && f (xs, ys, n + 1))))

-- Check is given element is a first element in a list of tuples
-- 1 [(1,2), (2, 3)] => True
-- 3 [(1,2), (2, 3)] => False
fstTupleElem :: Eq a => a -> Rel a -> Bool
fstTupleElem _ [] = False
fstTupleElem n (x:xs) = (n == fst x) || fstTupleElem n xs

prop_isSerialCheck :: [Int] -> Rel Int -> Property
prop_isSerialCheck xs ys = length xs > 2 && length ys > 2
  && all (\tuple -> elem (fst tuple) xs && elem (snd tuple) xs) ys ==>
    isSerial xs ys


-- R = {(x, y) | x = y(mod n)}  n > 0
-- We take a simple example:
-- 1 = 3 mod 2 => (1, 3)
-- 3 = 7 mod 4 => (3, 7)
-- 7 = 15 mod 8 => (7, 15)
-- The relations will only grow bigger, but the problem that arises is that
-- there must be an x ∈ R where (x, 1).
-- This can't be the case because you need to have y bigger than x in
-- order to make a valid case of x = y (mode n)

exerciseFour = do
  let relationA = [(1,2), (2,3), (3,1)]
  let domainA = [1,2,3]
  putStrLn $ "relation A: " ++ show relationA
  putStrLn $ "in domain: " ++ show domainA
  putStrLn $ "isSerial?: " ++ show (isSerial domainA relationA)
  let relationB = [(1,2), (2,3)]
  let domainB = [1,2,3]
  putStrLn $ "relation B: " ++ show relationB
  putStrLn $ "in domain: " ++ show domainB
  putStrLn $ "isSerial?: " ++ show (isSerial domainB relationB)
  let relationC = [(1,2), (2,3), (3,1)]
  let domainC = [3,4,5,6]
  putStrLn $ "relation B: " ++ show relationC
  putStrLn $ "in domain: " ++ show domainC
  putStrLn $ "isSerial?: " ++ show (isSerial domainC relationC)
  quickCheck prop_isSerialCheck
-- =============================================================================
-- TIME SPENT ~ 5 hour
-- =============================================================================


-- =============================================================================
-- EXERCISE 5
-- =============================================================================
-- RESULTS

-- *Main> exerciseFive
-- Example from exercise 6
-- input [(1,2),(2,3),(3,4)]
-- output [(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]
-- Result: True
-- input [(1,1),(2,2),(3,3),(4,4)]
-- output [(1,1),(2,2),(3,3),(4,4)]
-- Result: True
-- input [(1,2),(2,1),(2,3),(3,2)]
-- output [(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)]
-- Result: True

-- =============================================================================
-- IMPLEMENTATION
-- Use the datatype for relations from the previous exercise, plus

--  E.g., trClos [(1,2),(2,3),(3,4)] should give [(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)].

infixr 5 @@

(@@) :: Eq a => Rel a -> Rel a -> Rel a
r @@ s =  nub [ (x,z) | (x,y) <- r, (w,z) <- s, y == w ]

--  (x,y) ∈ A && (y,z) ∈ A -> (x,z) ∈ A
trClos :: Ord a => Rel a -> Rel a
-- First check for the pairs if there is a relation (x,y) ∈ A && (y,z) ∈ A where y == y
-- If true then create pair (x, z)
-- Remove all duplicates
-- Do this in recursion, because new pairs can be formed that form the relation (x,y) ∈ A && (y,z) ∈ A where y == y
-- Run recursion till the result can no longer be sorted
trClos = fp (\xs -> sort (nub (xs ++ xs @@ xs)))

exerciseFive = do
    putStrLn "Example from exercise 6"
    let exampleOne = [(1,2),(2,3),(3,4)]
    let resultOne = [(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]
    putStrLn $ "input " ++ show exampleOne
    putStrLn $ "output " ++ show resultOne
    putStrLn $ "Result: " ++ show (trClos exampleOne == resultOne)
    let exampleTwo = [(1,1), (2,2), (3,3), (4,4)]
    let resultTwo = [(1,1), (2,2), (3,3), (4,4)]
    putStrLn $ "input " ++ show exampleTwo
    putStrLn $ "output " ++ show resultTwo
    putStrLn $ "Result: " ++ show (trClos exampleTwo == resultTwo)
    let exampleThree = [(1,2), (2,1), (2,3), (3,2)]
    let resultThree = [(1,1), (1,2), (1,3), (2,1), (2,2), (2,3), (3,1), (3,2), (3,3)]
    putStrLn $ "input " ++ show exampleThree
    putStrLn $ "output " ++ show resultThree
    putStrLn $ "Result: " ++ show (trClos exampleThree == resultThree)
-- =============================================================================
-- TIME SPENT ~ 4 hour
-- =============================================================================


-- =============================================================================
-- EXERCISE 6
-- =============================================================================
-- RESULTS

-- *Main> exerciseSix
-- "QuickCheck for symClos function"
-- +++ OK, passed 100 tests.
-- "QuickCheck for trClos function"
-- +++ OK, passed 100 tests.

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
-- =============================================================================
-- TIME SPENT ~ 4 hour
-- =============================================================================


-- =============================================================================
-- EXERCISE 7
-- =============================================================================
-- RESULTS

-- *Main> exerciseSeven
-- Exercise 7
-- QuickCheck implementation
-- *** Failed! Falsified (after 2 tests and 1 shrink):
-- [(0,1)]

-- =============================================================================
-- IMPLEMENTATION
-- Is there a difference between the symmetric closure of the transitive
-- closure of a relation R and the transitive closure of the symmetric
-- closure of R ?

testComparison :: (Ord a) => Rel a -> Bool
testComparison xs = symClos(trClos xs) == trClos (symClos xs)

-- There is a difference between the symmetric closure of the transitive closure of a relation R
-- and the transitive closure of the symmetric closure of R.
-- If we give symClos a random input and we give the same random input to
-- trClos they return different values.

-- E.g [(0,1)]

-- symmetry = [(0,1), (1,0)]
-- transitive = [(0,0), (0,1), (1,0), (1,1)]

-- transitive = [(0,1)]
-- symmetry = [(0,1), (1,0)]
exerciseSeven = do
  putStrLn "Exercise 7"
  putStrLn "QuickCheck implementation"
  quickCheck (testComparison :: Rel Int -> Bool)
-- =============================================================================
-- TIME SPENT ~ 1 hour
-- =============================================================================

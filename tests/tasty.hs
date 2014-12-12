{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module Main where 

import Test.Tasty
import Test.Tasty.QuickCheck
import Projection
import Prelude hiding ((<=))
import Poset
import Data.DeriveTH

derive makeArbitrary ''ProjBool

main :: IO ()
main = defaultMain tests 

type TestPoset = ProjBool

tests :: TestTree
tests = testGroup "allTests"
   [posetTests (undefined :: ProjBool) "ProjBool",
    uLatticeTests (undefined :: ProjBool) "ProjBool",
    lLatticeTests (undefined :: ProjBool) "ProjBool"
   ]



idempotency :: Eq a => (a -> a -> a) -> a -> Bool
idempotency f a = f a a == a

associativity :: Eq a => (a -> a -> a) -> a -> a -> a-> Bool
associativity f a b c = f (f a b) c == f a (f b c)

commutativity :: Eq a => (a -> a -> a) -> a -> a -> Bool
commutativity f a b = f a b == f b a



posetAntisymmetry :: Poset a => a -> a -> Bool
posetAntisymmetry = antisymmetry (<=)

posetTransitivity :: Poset a => a -> a -> a -> Property
posetTransitivity  = transitivity (<=)

posetReflexivity :: Poset a => a -> Bool
posetReflexivity = reflexivity (<=)

antisymmetry :: Eq a => (a -> a -> Bool) -> a -> a -> Bool
antisymmetry p a b = ( p a b && p b a ) == (b == a)

transitivity :: (a -> a -> Bool) -> a -> a -> a -> Property 
transitivity p a b c = p a b && p b c ==> p a c

reflexivity :: (a -> a -> Bool) -> a -> Bool
reflexivity p a = p a a

lessThanBoth :: (a -> a -> Bool) -> a -> a -> a -> Bool
lessThanBoth lt c a b = c `lt` a && c `lt` b 

greatestSuch :: Eq a => (a -> a -> Bool) -> (a -> a -> a) -> a -> a -> a -> Property
greatestSuch lt f a b c =  lessThanBoth lt c a b ==> c `lt` (f a b) 

uLatticeTests :: (Show t, ULattice t, Arbitrary t) => t -> String -> TestTree
uLatticeTests (_ :: t) posetName = testGroup ("Upper SemiLattice Tests: " ++ posetName)
  [ testProperty "Upper Lattice Associativity" $
    \x -> associativity (\/) (x :: t),
    testProperty "Upper Lattice Commutativity" $
    \x -> commutativity (\/) (x :: t),
    testProperty "Upper Lattice Idempotence" $
    \x -> idempotency (\/) (x :: t),
    testProperty "Upper Lattice Greater Than Both" $
    \x y -> lessThanBoth (flip (<=))  (x \/ y) (x :: t) y,
    testProperty "Upper Lattice Least Upper Bound" $
    \x -> greatestSuch (flip (<=)) (\/) (x :: t)
  ]

lLatticeTests :: (Show t, LLattice t, Arbitrary t) => t -> String -> TestTree
lLatticeTests (_ :: t) posetName = testGroup ("Lower SemiLattice Tests: " ++ posetName)
  [ testProperty "Lower Lattice Associativity" $
    \x -> associativity (/\) (x :: t),
    testProperty "Lower Lattice Commutativity" $
    \x -> commutativity (/\) (x :: t),
    testProperty "Lower Lattice Idempotence" $
    \x -> idempotency (/\) (x :: t),
    testProperty "Lower Lattice Greater Than Both" $
    \x y -> lessThanBoth (<=)  (x /\ y) (x :: t) y,
    testProperty "Lower Lattice Least Lower Bound" $
    \x -> greatestSuch (<=) (/\) (x :: t)
  ]

posetTests :: (Show t, Poset t, Arbitrary t) => t -> String -> TestTree
posetTests (_ :: t) posetName = testGroup ("Poset Tests: " ++ posetName)
  [ testProperty "Poset Antisymmetry" $
       \x -> posetAntisymmetry (x :: t),
    testProperty "Poset Transitivity" $
       \x -> posetTransitivity (x :: t),
    testProperty "Poset Reflexivity" $
       \x -> posetReflexivity (x :: t)
  ]


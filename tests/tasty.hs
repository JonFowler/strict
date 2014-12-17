{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module Main where 

import Test.Tasty
import Test.Tasty.QuickCheck
import Projection
import Prelude hiding ((<=))
import Poset
import Data.DeriveTH

derive makeArbitrary ''FlatProj
derive makeArbitrary ''FlatVal
derive makeArbitrary ''Str
derive makeArbitrary ''FailVal
--derive makeArbitrary ''BVar
--derive makeArbitrary ''BoolExp

instance CoArbitrary a => CoArbitrary (FlatVal a) where
  coarbitrary BottomF = variant (1 :: Int)
  coarbitrary (ValF a) = variant (2 :: Int) . coarbitrary a

instance CoArbitrary a => CoArbitrary (FailVal a) where
  coarbitrary Fail = variant (1 :: Int)
  coarbitrary (Pure a) = variant (2 :: Int) . coarbitrary a

main :: IO ()
main = defaultMain tests 

type TestPoset = ProjBool

--evalProj :: BoolExp -> ProjBool -> ValBool -> ValBool -> ValBool -> Property
--evalProj e p b1 b2 b3 = let q = projB e Var1 p in
--  all (/= FailureF) [b1, b2, b3] ==>
--  applyProj p (evalB e b1 b2 b3) == applyProj p (evalB e (applyProj q b1) b2 b3)
--
--evalProj2 :: BoolExp -> ProjBool -> ValBool -> ValBool -> ValBool -> Property
--evalProj2 e p b1 b2 b3 = let q = projB2 e Var1 p in
--  all (/= FailureF) [b1, b2, b3] ==>
--  applyProj p (evalB e b1 b2 b3) == applyProj p (evalB e (applyProj q b1) b2 b3)
--
--projRulesEquiv :: BoolExp -> ProjBool -> Bool
--projRulesEquiv e p = projB e Var1 p == projB2 e Var1 p

tests :: TestTree
tests = testGroup "allTests"
   [
    posetTests (undefined :: ProjBool) "ProjBool",
    uLatticeTests (undefined :: ProjBool) "ProjBool",
    lLatticeTests (undefined :: ProjBool) "ProjBool",
    distributiveTests (undefined :: ProjBool) "ProjBool",
    posetTests (undefined :: FlatVal Bool) "Flat Value Bool",
    posetTests (undefined :: FlatVal Bool -> FlatVal Bool) "Flat Value Bool",
    testProperty "ProjBool represents projection" $
      \x -> represents (<=) (<=) applyP (x :: ProjBool),
    testProperty "AndProj represents And projection" $
      \x -> represents2 andProj andFunc applyP (x :: ProjBool)
--
--    testProperty "Bool projection 2 works" $
--      evalProj2,
--    testProperty "Bool projection works" $
--      evalProj,
--    testProperty "Projection rules equivalent" $
--      projRulesEquiv
   ]

instance (Finite a, Show a, Show b) => Show (a -> b) where
  show f = show [ show x ++ " -> " ++ show (f x) | x <- allVals ]

idempotency :: Eq a => (a -> a -> a) -> a -> Bool
idempotency f a = f a a == a

associativity :: Eq a => (a -> a -> a) -> a -> a -> a-> Bool
associativity f a b c = f (f a b) c == f a (f b c)

commutativity :: Eq a => (a -> a -> a) -> a -> a -> Bool
commutativity f a b = f a b == f b a

represents :: (a -> a -> Bool) -> (b -> b -> Bool) -> (a -> b) -> a -> a -> Bool
represents f g conv a b = f a b == g (conv a) (conv b)

represents2 :: Eq b => (a -> a -> a) -> (b -> b -> b) -> (a -> b) -> a -> a -> Bool
represents2 f g conv a b = conv (f a b) == g (conv a) (conv b) 

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

distributesOver :: Eq a => (a -> a -> a) -> (a -> a -> a) -> a -> a -> a-> Bool
distributesOver f g a b c = f a (g b c) == g (f a b) (f a c)

distributiveTests :: (Show t, Lattice t, Arbitrary t) => t -> String -> TestTree
distributiveTests (_ :: t) name = testGroup ("Lattice Tests: " ++ name) $
  [ testProperty "Lattice Distributivity" $
     \x -> ((/\) `distributesOver` (\/)) (x :: t),
    testProperty "Lattice Distributivity" $
     \x -> ((\/) `distributesOver` (/\)) (x :: t)
          
  ]

uLatticeTests :: (Show t, ULattice t, Arbitrary t) => t -> String -> TestTree
uLatticeTests (_ :: t) name = testGroup ("Upper SemiLattice Tests: " ++ name)
  [ testProperty "Upper Lattice Associativity" $
    \x -> associativity (\/) (x :: t),
    testProperty "Upper Lattice Commutativity" $
    \x -> commutativity (\/) (x :: t),
    testProperty "Upper Lattice Idempotence" $
    \x -> idempotency (\/) (x :: t),
    testProperty "Upper Lattice Greater Than Both" $
    \x y -> lessThanBoth (flip (<=))  (x \/ y) (x :: t) y,
    testProperty "Upper Lattice Least Upper Bound" $
    \x -> greatestSuch (flip (<=)) (\/) (x :: t),
    testProperty "Upper Lattice Top" $
    \x -> (x :: t) <= top 
  ]

lLatticeTests :: (Show t, LLattice t, Arbitrary t) => t -> String -> TestTree
lLatticeTests (_ :: t) name = testGroup ("Lower SemiLattice Tests: " ++ name)
  [ testProperty "Lower Lattice Associativity" $
    \x -> associativity (/\) (x :: t),
    testProperty "Lower Lattice Commutativity" $
    \x -> commutativity (/\) (x :: t),
    testProperty "Lower Lattice Idempotence" $
    \x -> idempotency (/\) (x :: t),
    testProperty "Lower Lattice Greater Than Both" $
    \x y -> lessThanBoth (<=)  (x /\ y) (x :: t) y,
    testProperty "Lower Lattice Least Lower Bound" $
    \x -> greatestSuch (<=) (/\) (x :: t),
    testProperty "Lower Lattice Bottom" $
    \x -> bottom <= (x :: t)
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



module Poset where

import Prelude hiding (Ord(..))

class Poset a => LLattice a where
  (/\) :: a -> a -> a

class Poset a => ULattice a where
  (\/) :: a -> a -> a

class Poset a where
  (<=) :: a -> a -> Bool

class (LLattice a, ULattice a) => Lattice a

data Bottom a = Bottom | Pure a

instance Poset a => Poset (Bottom a) where
  Bottom <= _ = True
  _ <= Bottom = False
  Pure a <= Pure b = a <= b

instance Poset Bool where
  (<=) = (==)

instance Poset a => LLattice (Bottom a) where
  Bottom /\ _ = Bottom
  _ /\ Bottom = Bottom
  Pure a /\ Pure b = if a <= b
                     then Pure a
                     else if b <= a
                          then Pure b
                          else Bottom
  

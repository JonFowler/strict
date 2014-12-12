module Poset where

import Prelude hiding (Ord(..))

class Poset a => LLattice a where
  (/\) :: a -> a -> a
  bottom :: a

class Poset a => ULattice a where
  (\/) :: a -> a -> a
  top :: a

class Eq a => Poset a where
  (<=) :: a -> a -> Bool

class (LLattice a, ULattice a) => Lattice a

instance Poset Bool where
  (<=) = (==)


{-# LANGUAGE TypeFamilies #-}

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

data ProjBool
  = IDBool
  | BotBool
  | TrueOnly
  | FalseOnly

projBool :: ProjBool -> Bottom Bool -> Bottom Bool
projBool IDBool a = a
projBool BotBool _ = Bottom
projBool TrueOnly (Pure True) = Pure True
projBool TrueOnly _ = Pure True
projBool FalseOnly (Pure False) = Pure False
projBool FalseOnly _ = Pure False




data family Proj a 

class Projection a where
  idProj :: Proj a -> Proj a
  botProj :: Proj a -> Proj a


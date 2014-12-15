{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Projection where

import Poset
import Prelude hiding ((<=))

data Exp
  = If Exp Exp Exp
  | ValB Bool
  | ValL List 
--  | Ap Fun [Exp]
  | Fix [Exp] 
  | Var VarId

data List = Emp | Cons Exp Exp

data Fun = Fun
  { vars :: [ VarId ],
    body :: Exp
  }

newtype VarId = VarId Int deriving (Eq, Show, Read, Num)

data Proj = ProjB ProjBool
          | ProjL ProjList 

data FlatProj a 
  = FailF
  | IdF
  | AbsF
  | StrF
  | StrVal a
  | AbsVal a
  deriving (Eq, Show)

data FlatVal a
  = FailureF
  | BottomF
  | ValF a
  deriving (Eq, Show)

applyProj :: Eq a => FlatProj a -> FlatVal a -> FlatVal a
applyProj FailF _ = FailureF
applyProj IdF a = a
applyProj AbsF FailureF = FailureF
applyProj AbsF _ = BottomF
applyProj StrF BottomF = FailureF
applyProj StrF a = a
applyProj (StrVal a) (ValF b) 
  | a == b = ValF b
applyProj (StrVal _) _ = FailureF
applyProj (AbsVal a) (ValF b)
  | a == b = ValF b
applyProj (AbsVal _) FailureF = FailureF
applyProj (AbsVal _) _ = BottomF

instance Eq a => Poset (FlatVal a) where
  FailureF <= _ = True
  BottomF <= ValF _ = True
  ValF a <= ValF b = a == b
  _ <= _ = False

class Finite a where
  allVals :: [ a ]

instance Finite Bool where
  allVals = [False, True]

instance Finite a => Finite (FlatVal a) where
  allVals = [FailureF, BottomF] ++ [ValF a | a <- allVals  ]

instance (Finite a, Eq b) => Eq (a -> b) where
  f == g = and [f x == g x | x <- allVals ]

instance (Finite a, Poset b) => Poset (a -> b) where
  f <= g = and [ f x <= g x | x <- allVals ] 

type ProjBool = FlatProj Bool


instance Eq a => Poset (FlatProj a) where
  FailF <= _ = True
  _ <= IdF = True
  AbsF <= AbsVal _ = True
  StrVal _ <= StrF = True
  StrVal a <= AbsVal b = a == b
  a <= b = a == b 

instance Eq a => LLattice (FlatProj a) where
  a /\ b
    | a <= b = a
    | b <= a = b
  AbsVal _ /\ AbsVal _ = AbsF
  AbsVal a /\ StrF = StrVal a
  StrF /\ AbsVal a = StrVal a
  _ /\ _ = FailF

  bottom = FailF
--
--
instance Eq a => ULattice (FlatProj a) where
  a \/ b
    | a <= b = b
    | b <= a = a
  StrVal _ \/ StrVal _ = StrF 
  StrVal a \/ AbsF = AbsVal a
  AbsF \/ StrVal a = AbsVal a
  _ \/ _ = IdF
 
  top = IdF

instance Eq a => Lattice (FlatProj a)

(&+&) :: Proj -> Proj -> Proj
ProjB a &+& ProjB b = ProjB (a \/ b) 
_ &+& _ = error "not ProjBool"



       

data ProjList = ConsL
  

proj ::  Fun -> Int -> Proj -> Proj
proj f i alpha = undefined f i alpha



  

    

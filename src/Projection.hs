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

--(&+&) :: Proj -> Proj -> Proj
--ProjB a &+& ProjB b = ProjB (a \/ b) 
--_ &+& _ = error "not ProjBool"

       

data ProjList = ConsL
  

proj ::  Fun -> Int -> Proj -> Proj
proj f i alpha = undefined f i alpha



  

    

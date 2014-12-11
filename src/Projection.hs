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

data ProjBool
  = FailB
  | AbsB
  | StrB
  | IdB deriving (Eq, Show)

instance Poset ProjBool where
  FailB <= _ = True
  AbsB <= AbsB = True
  StrB <= StrB = True
  _ <= IdB = True
  _ <= _ = False

instance LLattice ProjBool where
  FailB /\ _ = FailB
  _ /\ FailB = FailB
  IdB /\ a = a
  a /\ IdB = a
  a /\ b = if a == b then a else FailB

instance ULattice ProjBool where
  FailB \/ a = a
  a \/ FailB = a
  IdB \/ _ = IdB 
  _ \/ IdB = IdB
  a \/ b = if a == b then a else IdB

(&&) :: Proj -> Proj -> Proj
ProjB a && ProjB b = ProjB (a \/ b) 
_ && _ = error "not ProjBool"

       
instance Lattice ProjBool

data ProjList
  

proj ::  Fun -> Int -> Proj -> Proj
proj f i alpha = undefined f i alpha



  

    

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
  | TrueB
  | FalseB
  | ATrueB
  | AFalseB
  | IdB deriving (Eq, Show)

instance Poset ProjBool where
  FailB <= _ = True
  _ <= IdB = True
  FalseB <= AFalseB = True
  TrueB <= ATrueB = True
  FalseB <= StrB = True
  TrueB <= StrB = True
  AbsB <= ATrueB  = True
  AbsB <= AFalseB = True
  a <= b
    | a == b = True
    | otherwise = False
  

instance LLattice ProjBool where
  AFalseB /\ StrB = FalseB
  StrB /\ AFalseB = FalseB
  ATrueB /\ StrB = TrueB
  StrB /\ ATrueB = TrueB
  a /\ b
    | a <= b = a
    | b <= a = b
  _ /\ _ = FailB

  bottom = FailB


instance ULattice ProjBool where
  AbsB \/ FalseB = AFalseB
  FalseB \/ AbsB = AFalseB
  AbsB \/ TrueB = ATrueB
  TrueB \/ AbsB = ATrueB
  a \/ b
    | a <= b = b 
    | b <= a = a 
  _ \/ _ = IdB 

  top = IdB

(&+&) :: Proj -> Proj -> Proj
ProjB a &+& ProjB b = ProjB (a \/ b) 
_ &+& _ = error "not ProjBool"

       
instance Lattice ProjBool

data ProjList = ConsL
  

proj ::  Fun -> Int -> Proj -> Proj
proj f i alpha = undefined f i alpha



  

    

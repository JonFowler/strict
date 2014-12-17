{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}

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

--data Proj = ProjB ProjBool
--          | ProjL ProjList 

data FlatProj a 
  = IdFP
  | FailFP
  | ValFP a
  deriving (Eq, Show)

data Str
  = Abs
  | Str
  deriving (Eq, Show)

data FailVal a
  = Fail
  | Pure a
  deriving (Eq, Show)

data FlatVal a
  = BottomF
  | ValF a
  deriving (Eq, Show)

applyFP :: Eq a => FlatProj a -> FlatVal a -> FlatVal a
applyFP IdFP a = a
applyFP (ValFP a) (ValF b)
  | a == b = ValF b 
applyFP _ _ = BottomF

class (Lattice a)  => Projection a where
  type ValP a :: *
  applyP :: a -> ValP a -> ValP a

instance Eq a => Projection (FlatProj a) where
  type ValP (FlatProj a) = FlatVal a
  applyP IdFP a = a
  applyP (ValFP a) (ValF b)
    | a == b = ValF b 
  applyP _ _ = BottomF
----
----  bottomP = undefined
--
--newtype StrProj a = StrProj (Str, a)
----
instance (Projection a, LLattice (ValP a)) => Projection (Str, a) where
  type ValP (Str, a) = FailVal (ValP a)
  applyP _ Fail = Fail
  applyP (Abs, p) (Pure a) = Pure $ applyP p a
  applyP (Str, p) (Pure a) = let r = applyP p a in
    if r == bottom then Fail else Pure r

instance Poset Str where
  Abs <= Str = False 
  _ <= _ = True 
   
instance Eq a => Poset (FlatVal a) where
  BottomF <= _ = True
  ValF a <= ValF b = a == b
  ValF _ <= BottomF = False

instance Poset a => Poset (FailVal a) where
  Fail <= _ = True
  Pure a <= Pure b = a <= b
  Pure _ <= Fail = False

class Finite a where
  allVals :: [ a ]

instance Finite Bool where
  allVals = [False, True]

instance Finite a => Finite (FailVal a) where
  allVals = Fail : [Pure a | a <- allVals]

instance Finite a => Finite (FlatVal a) where
  allVals = BottomF : [ValF a | a <- allVals  ]

instance (Finite a, Eq b) => Eq (a -> b) where
  f == g = and [f x == g x | x <- allVals ]

instance (Finite a, Poset b) => Poset (a -> b) where
  f <= g = and [ f x <= g x | x <- allVals ] 

type ProjBool = (Str, FlatProj Bool)

type ValBool = FailVal (FlatVal Bool)

instance Eq a => Poset (FlatProj a) where
  FailFP <= _ = True
  _ <= IdFP = True
  ValFP a <= ValFP b
    | a == b = True
  _ <= _ = False

instance (Poset a, Poset b) => Poset (a, b) where
  (a1, a2) <= (b1, b2) = a1 <= b1 && a2 <= b2

instance Eq a => LLattice (FlatVal a) where
  a /\ b
    | a <= b = a
    | b <= a = b
  _ /\ _ = BottomF 
  bottom = BottomF

instance Eq a => LLattice (FlatProj a) where
  a /\ b
    | a <= b = a
    | b <= a = b
  _ /\ _ = FailFP

  bottom = FailFP

instance LLattice Str where
  a /\ b
    | a <= b = a
    | b <= a = b
    | otherwise = error "not correct"
  bottom = Str
  
instance Eq a => ULattice (FlatProj a) where
  a \/ b
    | a <= b = b
    | b <= a = a
  _ \/ _ = IdFP
 
  top = IdFP

instance ULattice Str where
  a \/ b
    | a <= b = b
    | b <= a = a
  _ \/ _ = Abs 
 
  top = Abs 

instance (LLattice m, LLattice n) => LLattice (m, n) where
  (a1, a2) /\ (b1, b2) = (a1 /\ b1, a2 /\ b2)
  bottom = (bottom, bottom)

instance (ULattice m, ULattice n) => ULattice (m, n) where
  (a1, a2) \/ (b1, b2) = (a1 \/ b1, a2 \/ b2)
  top = (top, top)

instance Eq a => Lattice (FlatProj a)
instance Lattice Str
instance (Lattice m, Lattice n) => Lattice (m, n)

andProj :: Lattice b => (Str,b) -> (Str,b) -> (Str,b)
andProj (Str,b1) (Str,b2) = (Str , b1 /\ b2)
andProj (Str,b1) (Abs,_) = (Str, b1)
andProj (Abs,_) (Str,b2) = (Str, b2)
andProj (Abs,b1) (Abs,b2) = (Abs, b1 \/ b2)

--
--andFlatProj :: Eq a => FlatProj a -> FlatProj a -> FlatProj a
--andFlatProj FailF _ = FailF
--andFlatProj _ FailF = FailF
--andFlatProj AbsF StrF = StrF
--andFlatProj StrF AbsF = StrF
--andFlatProj (StrVal a) IdF = StrVal a
--andFlatProj IdF (StrVal a) = StrVal a
--andFlatProj IdF (AbsVal _) = IdF
--andFlatProj (AbsVal _) IdF = IdF
--andFlatProj (StrVal a) (StrVal b)
--  | a == b = StrVal a
--  | otherwise = FailF
--andFlatProj (AbsVal a) (AbsVal b)
--  | a == b = AbsVal a
--  | otherwise = IdF
--andFlatProj (AbsVal _) (StrVal b) = StrVal b
--andFlatProj (StrVal a) (AbsVal _) = StrVal a
--andFlatProj AbsF IdF = IdF
--andFlatProj IdF AbsF = IdF
--andFlatProj StrF IdF = StrF
--andFlatProj IdF StrF = StrF
--andFlatProj (AbsVal a) AbsF = AbsVal a
--andFlatProj AbsF (AbsVal a) = AbsVal a 
--andFlatProj (StrVal a) AbsF = StrVal a
--andFlatProj AbsF (StrVal a) = StrVal a
--andFlatProj StrF (StrVal a) = StrVal a
--andFlatProj (StrVal a) StrF = StrVal a
--andFlatProj StrF (AbsVal _) = StrF
--andFlatProj (AbsVal _) StrF = StrF
--andFlatProj IdF IdF = IdF
--andFlatProj AbsF AbsF = AbsF
--andFlatProj StrF StrF = StrF
type ValFail a = FailVal (FlatVal a) 
--
andFunc :: Eq a => (ValFail a -> ValFail a) -> (ValFail a -> ValFail a) -> ValFail a -> ValFail a 
andFunc f g x
  | f x == Fail || g x == Fail = Fail
  | f x <= g x = g x 
  | g x <= f x = f x
  | otherwise = error "Function not projection"
--
--
--(&+&) :: Proj -> Proj -> Proj
--ProjB a &+& ProjB b = ProjB (andFlatProj a b) 
--_ &+& _ = error "not ProjBool"
--
--data ProjList = ConsL
--  
--data BoolExp
--  = BIf BoolExp BoolExp BoolExp
--  | BVar BVar
--  | BVal Bool deriving (Eq, Show)
--
--data BVar = Var1 | Var2 | Var3 deriving (Eq, Show)
--
--guardB :: ProjBool -> ProjBool -> ProjBool
--guardB FailF _ = FailF
--guardB AbsF _ = AbsF
--guardB p q = q \/ (AbsF /\ p) 
--
--evalB :: BoolExp -> ValBool -> ValBool -> ValBool -> ValBool
--evalB (BVar Var1) b1 _  _  = b1
--evalB (BVar Var2) _  b2 _  = b2
--evalB (BVar Var3) _  _  b3 = b3
--evalB (BVal b) _  _  _  = ValF b
--evalB (BIf e1 e2 e3) b1 b2 b3 = case evalB e1 b1 b2 b3 of
--  FailureF -> FailureF
--  BottomF -> BottomF
--  ValF True -> evalB e2 b1 b2 b3
--  ValF False -> evalB e3 b1 b2 b3
--
--projB :: BoolExp -> BVar -> ProjBool -> ProjBool
--projB b x p = guardB p (projB' b x (StrF /\ p))
--
--projB2 :: BoolExp -> BVar -> ProjBool -> ProjBool
--projB2 b x p = guardB p (projB2' b x (StrF /\ p))
--
--projB' :: BoolExp -> BVar -> ProjBool -> ProjBool
--projB' (BVar x) y p
--  | x == y = p
--  | otherwise = AbsF
--projB' (BVal _) _ _ = AbsF
--projB' (BIf e0 e1 e2) x p = projB e0 x StrF `andFlatProj` (projB e1 x p \/ projB e2 x p)
--
--projB2' :: BoolExp -> BVar -> ProjBool -> ProjBool
--projB2' (BVar x) y p
--  | x == y = p
--  | otherwise = AbsF
--projB2' (BVal _) _ _ = AbsF
--projB2' (BIf e0 e1 e2) x p =
--  (projB2 e0 x (StrVal True) `andFlatProj` projB2 e1 x p) \/
--  (projB2 e0 x (StrVal False) `andFlatProj` projB2 e2 x p)
--
--proj ::  Fun -> Int -> Proj -> Proj
--proj f i alpha = undefined f i alpha



  

    

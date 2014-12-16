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
  a <= b 
    | a == b = True
    | otherwise = False

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

type ValBool = FlatVal Bool

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

andFlatProj :: Eq a => FlatProj a -> FlatProj a -> FlatProj a
andFlatProj FailF _ = FailF
andFlatProj _ FailF = FailF
andFlatProj AbsF StrF = StrF
andFlatProj StrF AbsF = StrF
andFlatProj (StrVal a) IdF = StrVal a
andFlatProj IdF (StrVal a) = StrVal a
andFlatProj IdF (AbsVal _) = IdF
andFlatProj (AbsVal _) IdF = IdF
andFlatProj (StrVal a) (StrVal b)
  | a == b = StrVal a
  | otherwise = FailF
andFlatProj (AbsVal a) (AbsVal b)
  | a == b = AbsVal a
  | otherwise = IdF
andFlatProj (AbsVal _) (StrVal b) = StrVal b
andFlatProj (StrVal a) (AbsVal _) = StrVal a
andFlatProj AbsF IdF = IdF
andFlatProj IdF AbsF = IdF
andFlatProj StrF IdF = StrF
andFlatProj IdF StrF = StrF
andFlatProj (AbsVal a) AbsF = AbsVal a
andFlatProj AbsF (AbsVal a) = AbsVal a 
andFlatProj (StrVal a) AbsF = StrVal a
andFlatProj AbsF (StrVal a) = StrVal a
andFlatProj StrF (StrVal a) = StrVal a
andFlatProj (StrVal a) StrF = StrVal a
andFlatProj StrF (AbsVal _) = StrF
andFlatProj (AbsVal _) StrF = StrF
andFlatProj IdF IdF = IdF
andFlatProj AbsF AbsF = AbsF
andFlatProj StrF StrF = StrF

andFunc :: Eq a => (FlatVal a -> FlatVal a) -> (FlatVal a -> FlatVal a) -> FlatVal a -> FlatVal a 
andFunc f g x
  | f x == FailureF || g x == FailureF = FailureF
  | f x <= g x = g x 
  | g x <= f x = f x
  | otherwise = error "Function not projection"


(&+&) :: Proj -> Proj -> Proj
ProjB a &+& ProjB b = ProjB (andFlatProj a b) 
_ &+& _ = error "not ProjBool"

data ProjList = ConsL
  
data BoolExp
  = BIf BoolExp BoolExp BoolExp
  | BVar BVar
  | BVal Bool deriving (Eq, Show)

data BVar = Var1 | Var2 | Var3 deriving (Eq, Show)

guardB :: ProjBool -> ProjBool -> ProjBool
guardB FailF _ = FailF
guardB AbsF _ = AbsF
guardB p q = q \/ (AbsF /\ p) 

evalB :: BoolExp -> ValBool -> ValBool -> ValBool -> ValBool
evalB (BVar Var1) b1 _  _  = b1
evalB (BVar Var2) _  b2 _  = b2
evalB (BVar Var3) _  _  b3 = b3
evalB (BVal b) _  _  _  = ValF b
evalB (BIf e1 e2 e3) b1 b2 b3 = case evalB e1 b1 b2 b3 of
  FailureF -> FailureF
  BottomF -> BottomF
  ValF True -> evalB e2 b1 b2 b3
  ValF False -> evalB e3 b1 b2 b3

projB :: BoolExp -> BVar -> ProjBool -> ProjBool
projB b x p = guardB p (projB' b x (StrF /\ p))

projB2 :: BoolExp -> BVar -> ProjBool -> ProjBool
projB2 b x p = guardB p (projB2' b x (StrF /\ p))

projB' :: BoolExp -> BVar -> ProjBool -> ProjBool
projB' (BVar x) y p
  | x == y = p
  | otherwise = AbsF
projB' (BVal _) _ _ = AbsF
projB' (BIf e0 e1 e2) x p = projB' e0 x StrF `andFlatProj` (projB' e1 x p \/ projB' e2 x p)

projB2' :: BoolExp -> BVar -> ProjBool -> ProjBool
projB2' (BVar x) y p
  | x == y = p
  | otherwise = AbsF
projB2' (BVal _) _ _ = AbsF
projB2' (BIf e0 e1 e2) x p =
  (projB2' e0 x (StrVal True) `andFlatProj` projB2' e1 x p) \/
  (projB2' e0 x (StrVal False) `andFlatProj` projB2' e2 x p)

proj ::  Fun -> Int -> Proj -> Proj
proj f i alpha = undefined f i alpha



  

    

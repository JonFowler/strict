--{-# OPTIONS  --type-in-type #-}

module proj where

open import Level
open import Relation.Binary.PropositionalEquality

data FAlg : Set
data IAlg : Set where
  One' : IAlg 
  Zero' : IAlg 
  _⊕'_ : FAlg → FAlg → IAlg
  
data FAlg where
  In : IAlg → FAlg 
  _⊗_ : FAlg → FAlg → FAlg
  
One : FAlg
One = In One'

Zero : FAlg
Zero = In Zero'

_⊕_ : (a b : FAlg) → FAlg
a ⊕ b = In (a ⊕' b)
 
data Vals : FAlg → Set where
   one : Vals One 
   inL : {a b : FAlg} → Vals a → Vals (a ⊕ b)
   inR : {a b : FAlg} → Vals b → Vals (a ⊕ b)
   _,_ : {a b : FAlg} → Vals a → Vals b → Vals (a ⊗ b)
   
  
data BVals : FAlg → Set where
  one : BVals One
  bot⊕ : {a b : FAlg} → BVals (a ⊕ b)
  inL : {a b : FAlg} → BVals a → BVals (a ⊕ b)
  inR : {a b : FAlg} → BVals b → BVals (a ⊕ b)
  _,_ : {a b : FAlg} → BVals a → BVals b → BVals (a ⊗ b)
  


data Fail : FAlg → Set  where
  val : {a : FAlg} → BVals a → Fail a
  fail : {a : FAlg} → Fail a
   
data Hole : Set where
  hole : Hole
  _⊗-R_ : FAlg → Hole → Hole
  _⊗-L_ : Hole → FAlg → Hole
  
--record Inverse : 

--data HAlg : Hole → IAlg → FAlg → Set where
--  inF :  (a : IAlg)  → HAlg hole a (In a)  
--  onL : { h : Hole } → {i : IAlg} → { a b : FAlg} → HAlg h i a → HAlg (h ⊗-L b) i (a ⊗ b)
--  onR : { h : Hole } → {i : IAlg} → { a b : FAlg} → HAlg h i b → HAlg (a ⊗-R h) i (a ⊗ b)

--data Σ (A : Set) (B : A → Set) : Set where
--  _,_ : (a : A) → (b : B a) → Σ A B
--  
--data HAlg : Hole → FAlg → Set where
--  inF : ( a : IAlg ) → HAlg hole (In a)  
--  onL : { h : Hole } → {a b : FAlg} → HAlg h a → HAlg (h ⊗-L b) (a ⊗ b)
--  onR : { h : Hole } → {a b : FAlg} → HAlg h b → HAlg (a ⊗-R h) (a ⊗ b)
--  
--theR : {h : Hole} → (x : FAlg) →  Σ FAlg (HAlg h) → Σ FAlg (HAlg (x ⊗-R h))
--theL : {h : Hole} → (x : FAlg) →  Σ FAlg (HAlg h) → Σ FAlg (HAlg (h ⊗-L x))
--toF : (h : Hole) → IAlg → Σ FAlg (HAlg h)
--
--theR x (a , b) = (x ⊗ a) , onR b
--theL x (a , b) = (a ⊗ x) , onL b
--  
--toF hole a = (In a) , inF a
--toF (x ⊗-R h) a = theR x (toF h a) 
--toF (h ⊗-L x) a = theL x (toF h a) 
--
--fromF : (h : Hole)  → Σ FAlg (HAlg h) → IAlg
--fromF hole (._ , inF a) = a
--fromF (x ⊗-R h) (._ , onR {b = b} halg) = fromF h (b , halg)
--fromF (h ⊗-L x) (._ , onL {a = a} halg) = fromF h (a , halg) 
--
--fromREq : ∀ { a h} → (b : Σ FAlg (HAlg h)) → fromF (a ⊗-R h) (theR a b) ≡ fromF h b 
--fromREq (a₁ , c) = refl
--
--fromLEq : ∀ { a h} → (b : Σ FAlg (HAlg h)) → fromF (h ⊗-L a) (theL a b) ≡ fromF h b 
--fromLEq (a₁ , c) = refl
--
--leftID : ∀ x → (h : Hole)  → fromF h (toF h x) ≡ x
--leftID x hole = refl
--leftID x (a ⊗-R h) with leftID x h
--... | v = trans (fromREq (toF h x)) v 
--leftID x (h ⊗-L a) with leftID x h
--... | v = trans (fromLEq (toF h x)) v
--
----(λ { (u , v) → {!refl!}}) (toF h x)
--
--rightID : (h : Hole) → ∀ x  → toF h (fromF h x) ≡ x
--rightID hole (.(In a) , inF a) = refl 
--rightID (x ⊗-R h) (._ , onR {b = b} halg) with rightID h (b , halg)
--... | v = cong (theR x) v
--rightID (h ⊗-L x) (._ , onL {a = a} halg) with rightID h (a , halg)
--... | v = cong (theL x) v

--data _↦_ : FAlg → FAlg → Set where
--   -- Construction of output, note similarity to Vals rules
--   emp : {a : FAlg} → Zero ↦ a 
--   toOne : {a : FAlg} → a ↦ One
--   intoL : {a b c : FAlg} → a ↦ b → a ↦ (b ⊕ c)
--   intoR : {a b c : FAlg} → a ↦ c → a ↦ (b ⊕ c)
--   pairF : {a b c : FAlg} → a ↦ b → a ↦ c → a ↦ (b ⊗ c)
--
--   case : ∀ {a1 a2 ha1 ha2 ha1⊕ha2 c} → (h : Hole) →
--          HAlg h a1 ha1 → HAlg h a2 ha2 → HAlg h ((In a1) ⊕' (In a2)) ha1⊕ha2 →
--          ha1 ↦ c → ha2 ↦ c → ha1⊕ha2 ↦ c
----   case : {a b c : FAlg} → (h : Hole) → rep h a ↦ c → rep h b ↦ c → rep h (a ⊕ b) ↦ c
--------   
--fromLeft : {a b c : FAlg} → (a ⊕ b) ↦ c → a ↦ c
--fromLeft toOne = toOne
--fromLeft (intoL f) = intoL (fromLeft f)
--fromLeft (intoR f) = intoR (fromLeft f)
--fromLeft (pairF f g) = pairF (fromLeft f) (fromLeft g)
--fromLeft (case {a1 = a1} hole x1 x2 ⊕-H f1 f2) = {!!}
--fromLeft {a} {b} {c} (case (x ⊗-R h) x1 x2 ⊕-H f1 f2) = {!!}
--fromLeft (case (h ⊗-L x) x1 x2 ⊕-H f1 f2) = {!!}
--fromLeft (case Zero x₁ ⊕-H f1 f2) = f1
--fromLeft (case ⊕-H x₁ ⊕-H f1 f2) = f1 
--
--fromRight : {a b c : FAlg} → (a ⊕ b) ↦ c → a ↦ c
--fromRight toOne = toOne
--fromRight (intoL a₁) = intoL (fromRight a₁)
--fromRight (intoR a₁) = intoR (fromRight a₁)
--fromRight (pairF a₁ a₂) = pairF (fromRight a₁) (fromRight a₂)
--fromRight (case One x₁ ⊕-H a₁ a₂) = a₁
--fromRight (case Zero x₁ ⊕-H a₁ a₂) = a₁
--fromRight (case ⊕-H x₁ ⊕-H a₁ a₂) = a₁ 

--   
--_∘_ : {a b c : FAlg} → a ↦ b → b ↦ c → a ↦ c
--Zero ∘ Zero = Zero
--case x x₁ x₂ f f₁ ∘ Zero = {!!}
--f ∘ toOne = toOne
--f ∘ intoL g = intoL (f ∘ g)
--f ∘ intoR g = intoR (f ∘ g)
--f ∘ pairF g g₁ = pairF (f ∘ g) (f ∘ g₁)
--Zero ∘ case x x₁ x₂ g g₁ = Zero
--toOne ∘ case x x₁ () g g₁
--intoL f ∘ case {a1 = b} {ha1 = .b} x x₁ ⊕-H g g₁ = {!x!}
--intoR f ∘ case x x₁ ⊕-H g g₁ = {!!}
--pairF f f₁ ∘ case x x₁ x₂ g g₁ = {!!}
--case x x₁ x₂ f f₁ ∘ case x₃ x₄ x₅ g g₁ = {!!} 





--   
--fst : {a b : FAlg} → (a ⊗ b) ↦ a
--fst {One} = toOne
--fst {Zero} = {!!}
--fst {a1 ⊕ a2} {b} = case ( hole ⊗-L b ) {!!} {!!}
--fst {a ⊗ a₁} = {!!}
--   
--eval : {a b : FAlg} →  a ↦ b → Vals a → Vals b
--eval toOne a =  one
--eval Zero () 
--eval (intoL f) a = inL (eval f a)
--eval (intoR f) a = inR (eval f a)
--eval (pairF f1 f2) a = (eval f1 a) , (eval f2 a)
--eval (case h f g) a with read h a 
--eval (case h f g) a | inL v = eval f (insert h a v)
--eval (case h f g) a | inR v = eval g (insert h a v) 
--
--_>>=F_ : { a b : FAlg } →  Fail a → (BVals a → Fail b) → Fail b 
--_>>=F_ (val x) f = f x
--_>>=F_ fail f = fail
--
--mapF : { a b : FAlg } → (BVals a → BVals b) → Fail a → Fail b
--mapF f (val x) = val (f x)
--mapF f fail = fail
--
--evalB : {a b : FAlg} →  a ↦ b → BVals a → Fail b
--evalB Zero ()
--evalB toOne a = val one
--evalB (intoL f) a = mapF inL (evalB f a)
--evalB (intoR f) a = mapF inR (evalB f a)
--evalB (pairF f1 f2) a = (evalB f1 a) >>=F (λ x → 
--                        (evalB f2 a) >>=F (λ y →
--                        val (x , y))) 
--evalB (case h f g) a with readB h a
--evalB (case h f g) a | bot⊕ = fail
--evalB (case h f g) a | inL v = evalB f (insertB h a v)
--evalB (case h f g) a | inR v = evalB g (insertB h a v)
--
--data Proj : FAlg → Set where
--  one : Proj One
--  pairF : {a b : FAlg} → Proj a → Proj b → Proj (a ⊗ b)
----  _⊕-id_ : {a b : FAlg} → Proj a → Proj b → Proj (a ⊕ b)
----  _⊕-bot_ : {a b : FAlg} → Proj a → Proj b → Proj (a ⊕ b)
-- -- case-id : 
--  case-bot : {a b c : FAlg} → (h : Hole) → Proj (rep h a) → Proj (rep h b) → Proj (rep h (a ⊕ b))
--  id-bot : {a b c : FAlg} → (h : Hole) → Proj (rep h a) → Proj (rep h b) → Proj (rep h (a ⊕ b))
--  
--ProjtoFunc : {a : FAlg} → Proj a → a ↦ a
--ProjtoFunc one = toOne
--ProjtoFunc {One ⊗ One} (pairF p q) = pairF toOne toOne
--ProjtoFunc {Zero ⊗ One} (pairF p q) = pairF {!!} toOne
--ProjtoFunc {(a1 ⊕ a2) ⊗ One} (pairF p q) = pairF (case (hole ⊗-L One) 
--                           {!ProjtoFunc!} {!!}) {!!}
--ProjtoFunc {(a ⊗ a₁) ⊗ One} (pairF p p₁) = {!!}
--ProjtoFunc {a ⊗ b} (pairF p p₁) = {!!}
--ProjtoFunc (case-bot h p p₁) = {!!}
--ProjtoFunc (id-bot h p p₁) = {!!}




   
--   emp : {a : FAlg} → Zero ↦ a
--   oneTo : {a : FAlg} → One ↦ Zero 
--   _∘_ : {a b c : FAlg} → a ↦ b → b ↦ c → a ↦ c
--   _∘-L_ : {a b c d : FAlg} → a ↦ b → (b ⊗ d) ↦ c → (a ⊗ d) ↦ c
--   _∘-R_ : {a b c d : FAlg} → a ↦ b → (d ⊗ b) ↦ c → (d ⊗ a) ↦ c
   
   


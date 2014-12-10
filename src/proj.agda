--{-# OPTIONS  --type-in-type #-}

module proj where

open import Level
open import Relation.Binary.PropositionalEquality

data Type : Set
data IType : Set where
  One' : IType 
  Zero' : IType
  _⊕'_ : Type → Type → IType
  
data Type where
  In : IType → Type
  _⊗_ : Type → Type → Type 
  
One : Type 
One = In One'

Zero : Type 
Zero = In Zero'

_⊕_ : (a b : Type) → Type 
a ⊕ b = In (a ⊕' b)
 
data Vals : Type → Set where
   one : Vals One 
   inL : {a b : Type} → Vals a → Vals (a ⊕ b)
   inR : {a b : Type} → Vals b → Vals (a ⊕ b)
   _,_ : {a b : Type} → Vals a → Vals b → Vals (a ⊗ b)
  
data BVals : Type → Set where
  one : BVals One
  bot⊕ : {a b : Type} → BVals (a ⊕ b)
  inL : {a b : Type} → BVals a → BVals (a ⊕ b)
  inR : {a b : Type} → BVals b → BVals (a ⊕ b)
  _,_ : {a b : Type} → BVals a → BVals b → BVals (a ⊗ b)

data Fail : Type → Set  where
  val : {a : Type} → BVals a → Fail a
  fail : {a : Type} → Fail a
   
data Hole : Set where
  hole : Hole
  _⊗-R_ : Type → Hole → Hole
  _⊗-L_ : Hole → Type → Hole
  
data HType : Hole → IType → Type → Set where
  inF :  (a : IType)  → HType hole a (In a)  
  onL : { h : Hole } → {i : IType} → { a b : Type} → HType h i a → HType (h ⊗-L b) i (a ⊗ b)
  onR : { h : Hole } → {i : IType} → { a b : Type} → HType h i b → HType (a ⊗-R h) i (a ⊗ b)

--data Σ (A : Set) (B : A → Set) : Set where
--  _,_ : (a : A) → (b : B a) → Σ A B
--  
--data HType : Hole → Type → Set where
--  inF : ( a : IType ) → HType hole (In a)  
--  onL : { h : Hole } → {a b : Type} → HType h a → HType (h ⊗-L b) (a ⊗ b)
--  onR : { h : Hole } → {a b : Type} → HType h b → HType (a ⊗-R h) (a ⊗ b)
--  
--theR : {h : Hole} → (x : Type) →  Σ Type (HType h) → Σ Type (HType (x ⊗-R h))
--theL : {h : Hole} → (x : Type) →  Σ Type (HType h) → Σ Type (HType (h ⊗-L x))
--toF : (h : Hole) → IType → Σ Type (HType h)
--
--theR x (a , b) = (x ⊗ a) , onR b
--theL x (a , b) = (a ⊗ x) , onL b
--  
--toF hole a = (In a) , inF a
--toF (x ⊗-R h) a = theR x (toF h a) 
--toF (h ⊗-L x) a = theL x (toF h a) 
--
--fromF : (h : Hole)  → Σ Type (HType h) → IType
--fromF hole (._ , inF a) = a
--fromF (x ⊗-R h) (._ , onR {b = b} halg) = fromF h (b , halg)
--fromF (h ⊗-L x) (._ , onL {a = a} halg) = fromF h (a , halg) 
--
--fromREq : ∀ { a h} → (b : Σ Type (HType h)) → fromF (a ⊗-R h) (theR a b) ≡ fromF h b 
--fromREq (a₁ , c) = refl
--
--fromLEq : ∀ { a h} → (b : Σ Type (HType h)) → fromF (h ⊗-L a) (theL a b) ≡ fromF h b 
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

data _↦_ : Type → Type → Set where
   -- Construction of output, note similarity to Vals rules
--   emp : {a : Type} → Zero ↦ a 
   toOne : {a : Type} → a ↦ One
   intoL : {a b c : Type} → a ↦ b → a ↦ (b ⊕ c)
   intoR : {a b c : Type} → a ↦ c → a ↦ (b ⊕ c)
   pairF : {a b c : Type} → a ↦ b → a ↦ c → a ↦ (b ⊗ c)

   case : ∀ {a1 a2 ha1 ha2 ha1⊕ha2 c} → (h : Hole) →
          HType h a1 ha1 → HType h a2 ha2 → 
          HType h ((In a1) ⊕' (In a2)) ha1⊕ha2 →
          ha1 ↦ c → ha2 ↦ c → ha1⊕ha2 ↦ c
--   case : {a b c : Type} → (h : Hole) → rep h a ↦ c → rep h b ↦ c → rep h (a ⊕ b) ↦ c
------   
fromLeft : {a b c : Type} → (a ⊕ b) ↦ c → a ↦ c
fromLeft toOne = toOne
fromLeft (intoL f) = intoL (fromLeft f)
fromLeft (intoR f) = intoR (fromLeft f)
fromLeft (pairF f g) = pairF (fromLeft f) (fromLeft g)
fromLeft (case hole (inF a1) (inF a2) (inF .(In a1 ⊕' In a2)) f1 f2) 
   = f1
   
fromLeftH : ∀ {h a b hahb ha c} → 
           HType h a ha → HType h (In a ⊕' b) hahb
          → hahb ↦ c → ha ↦ c
fromLeftH h1 h2 toOne = toOne
fromLeftH h1 h2 (intoL f) = intoL (fromLeftH h1 h2 f)
fromLeftH h1 h2 (intoR f) = intoR (fromLeftH h1 h2 f)
fromLeftH h1 h2 (pairF f1 f2) = pairF (fromLeftH h1 h2 f1) (fromLeftH h1 h2 f2)
fromLeftH (inF a) (inF ._) (case .hole (inF .a) x2 (inF ._) f1 f2) = f1
fromLeftH (onL h1) (onL h2) (case ._ (onL x1) (onL x2) (onL x3) f1 f2)
 = {!!}
fromLeftH (onL h1) (onL h2) (case ._ x1 x2 (onR x3) f1 f2) 
  = case {!!} x1 x2 {!onR x3!} {!!} {!!}
fromLeftH (onR h1) h2 (case h₁ x1 x2 x3 f1 f2) = {!!}

fromRight : {a b c : Type} → (a ⊕ b) ↦ c → a ↦ c
fromRight toOne = toOne
fromRight (intoL a₁) = intoL (fromRight a₁)
fromRight (intoR a₁) = intoR (fromRight a₁)
fromRight (pairF a₁ a₂) = pairF (fromRight a₁) (fromRight a₂)
fromRight (case .hole (inF a) (inF a₁) (inF .(In a ⊕' In a₁)) f1 f2) 
  = f1 
  
data CaseOr : Hole → Type → IType → IType → Set where
  inL : ∀ {a c1 hc1 c2 h } → HType h c1 hc1 → 
                   (a ↦ hc1) → CaseOr h a c1 c2
  inR : ∀ {a c1 c2 hc2 h} → HType h c2 hc2 → 
                   (a ↦ hc2) → CaseOr h a c1 c2  
  case : ∀ {h h2 a1 a2 ha1 ha2 ha1⊕ha2 c1 c2 hc1c2} → 
          HType h (In c1 ⊕' In c2) hc1c2 →
          HType h2 a1 ha1 → HType h2 a2 ha2 → 
          HType h2 ((In a1) ⊕' (In a2)) ha1⊕ha2 →
          ha1 ↦ hc1c2 → ha2 ↦ hc1c2 → CaseOr h ha1⊕ha2 c1 c2 
          

lookIn : ∀ {a h hc12 c1 c2} → 
         HType h (In c1 ⊕' In c2) hc12 → 
         (a ↦ hc12) → CaseOr h a c1 c2
lookIn () toOne
lookIn {c1 = c1} (inF ._) (intoL f) = inL (inF c1) f
lookIn {c2 = c2} (inF ._) (intoR f) = inR (inF c2) f
lookIn (onL h) (pairF f1 f2) with lookIn h f1
lookIn (onL h) (pairF f1 f2) | inL ih if 
  = inL (onL ih) (pairF if f2)
lookIn (onL h) (pairF f1 f2) | inR ih if 
  = inR (onL ih) (pairF if f2)
lookIn (onL h₁) (pairF f1 f2) 
  | case h1 h2 h3 h4 g1 g2 
  = {!!}
--  = case (onL h1) h2 h3 h4 (pairF g1 {!fromLeft f2!}) {!!} 
lookIn (onR h) (pairF f1 f2) = {!!}
lookIn ht (case h2 x1 x2 x3 g1 g2) = case 
  ht x1 x2 x3 g1 g2
  
_∘_ : {a b c : Type} → b ↦ c → a ↦ b  → a ↦ c
toOne ∘ g = toOne
intoL f ∘ g = intoL (f ∘ g)
intoR f ∘ g = intoR (f ∘ g)
pairF f f₁ ∘ g = pairF (f ∘ g) (f₁ ∘ g)
case h x x1 () f1 f2 ∘ toOne
case .hole (inF a₁) x (inF ._) f1 f2 ∘ intoL g = f1 ∘ g
case .hole x (inF a₁) (inF ._) f1 f2 ∘ intoR g = f2 ∘ g 
case ._ (onL {h = h} x) (onL x1) (onL x2) f1 f2 ∘ pairF g1 g2 
  = {!!}
case ._ x x1 (onR x2) f1 f2 ∘ pairF g g₁ = {!!}
f ∘ case h x x1 x2 g1 g2 = case h x x1 x2 (f ∘ g1) (f ∘ g2)

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
--fst : {a b : Type} → (a ⊗ b) ↦ a
--fst {One} = toOne
--fst {Zero} = {!!}
--fst {a1 ⊕ a2} {b} = case ( hole ⊗-L b ) {!!} {!!}
--fst {a ⊗ a₁} = {!!}
--   
--eval : {a b : Type} →  a ↦ b → Vals a → Vals b
--eval toOne a =  one
--eval Zero () 
--eval (intoL f) a = inL (eval f a)
--eval (intoR f) a = inR (eval f a)
--eval (pairF f1 f2) a = (eval f1 a) , (eval f2 a)
--eval (case h f g) a with read h a 
--eval (case h f g) a | inL v = eval f (insert h a v)
--eval (case h f g) a | inR v = eval g (insert h a v) 
--
--_>>=F_ : { a b : Type } →  Fail a → (BVals a → Fail b) → Fail b 
--_>>=F_ (val x) f = f x
--_>>=F_ fail f = fail
--
--mapF : { a b : Type } → (BVals a → BVals b) → Fail a → Fail b
--mapF f (val x) = val (f x)
--mapF f fail = fail
--
--evalB : {a b : Type} →  a ↦ b → BVals a → Fail b
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
--data Proj : Type → Set where
--  one : Proj One
--  pairF : {a b : Type} → Proj a → Proj b → Proj (a ⊗ b)
----  _⊕-id_ : {a b : Type} → Proj a → Proj b → Proj (a ⊕ b)
----  _⊕-bot_ : {a b : Type} → Proj a → Proj b → Proj (a ⊕ b)
-- -- case-id : 
--  case-bot : {a b c : Type} → (h : Hole) → Proj (rep h a) → Proj (rep h b) → Proj (rep h (a ⊕ b))
--  id-bot : {a b c : Type} → (h : Hole) → Proj (rep h a) → Proj (rep h b) → Proj (rep h (a ⊕ b))
--  
--ProjtoFunc : {a : Type} → Proj a → a ↦ a
--ProjtoFunc one = toOne
--ProjtoFunc {One ⊗ One} (pairF p q) = pairF toOne toOne
--ProjtoFunc {Zero ⊗ One} (pairF p q) = pairF {!!} toOne
--ProjtoFunc {(a1 ⊕ a2) ⊗ One} (pairF p q) = pairF (case (hole ⊗-L One) 
--                           {!ProjtoFunc!} {!!}) {!!}
--ProjtoFunc {(a ⊗ a₁) ⊗ One} (pairF p p₁) = {!!}
--ProjtoFunc {a ⊗ b} (pairF p p₁) = {!!}
--ProjtoFunc (case-bot h p p₁) = {!!}
--ProjtoFunc (id-bot h p p₁) = {!!}




   
--   emp : {a : Type} → Zero ↦ a
--   oneTo : {a : Type} → One ↦ Zero 
--   _∘_ : {a b c : Type} → a ↦ b → b ↦ c → a ↦ c
--   _∘-L_ : {a b c d : Type} → a ↦ b → (b ⊗ d) ↦ c → (a ⊗ d) ↦ c
--   _∘-R_ : {a b c d : Type} → a ↦ b → (d ⊗ b) ↦ c → (d ⊗ a) ↦ c
   
   


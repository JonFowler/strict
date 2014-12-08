--{-# OPTIONS  --type-in-type #-}

module proj where

open import Level

data FAlg : Set where
  One : FAlg
  Zero : FAlg
  _⊕_ : FAlg → FAlg → FAlg
  _⊗_ : FAlg → FAlg → FAlg
 
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
  
rep : Hole → FAlg → FAlg
rep hole a = a
rep (x ⊗-R h) a = x ⊗ (rep h a)
rep (h ⊗-L x) a = (rep h a) ⊗ x

data Functor {x} (F : Set x  → Set x) : Set (suc x) where
    fmap : (∀ { A B} → (A → B) → F A → F B) → Functor F
    
--record RawFunctor (F : Set₁ → Set₁) : Set₂ where
--
--  field
--    fmap : ∀ {A B} → (A → B) → F A → F B


lens : {a b : FAlg} → {f : Set → Set} → (Functor f) → (h : Hole) → 
       (Vals a → f (Vals b)) → 
       Vals (rep h a) → f (Vals (rep h b))
lens fm hole upd a = upd a
lens (fmap f) (ak ⊗-R h) upd (a1 , a2) = f (λ x → (a1 , x)) (lens (fmap f) h upd a2)
lens (fmap f) (h ⊗-L ak) upd (a1 , a2) = f (λ x → (x , a2)) (lens (fmap f) h upd a1)

insert : {a b : FAlg} → (h : Hole)  → Vals (rep h a) → Vals b → Vals (rep h b)
insert hole s a = a
insert (x ⊗-R h) (s1 , s2) a = s1 , (insert h s2 a)
insert (h ⊗-L x) (s1 , s2) a = (insert h s1 a) , s2

read : {a : FAlg} → (h : Hole)  → Vals (rep h a) → Vals a
read hole a = a
read (x ⊗-R h) (_ , a) = read h a
read (h ⊗-L b) (a , _) = read h a

insertB : {a b : FAlg} → (h : Hole)  → BVals (rep h a) → BVals b → BVals (rep h b)
insertB hole s a = a
insertB (x ⊗-R h) (s1 , s2) a = s1 , (insertB h s2 a)
insertB (h ⊗-L x) (s1 , s2) a = (insertB h s1 a) , s2

readB : {a : FAlg} → (h : Hole)  → BVals (rep h a) → BVals a
readB hole a = a
readB (x ⊗-R h) (_ , a) = readB h a
readB (h ⊗-L b) (a , _) = readB h a
 
   
data _↦_ : FAlg → FAlg → Set where
   -- Construction of output, note similarity to Vals rules
   toOne : {a : FAlg} → a ↦ One
   intoL : {a b c : FAlg} → a ↦ b → a ↦ (b ⊕ c)
   intoR : {a b c : FAlg} → a ↦ c → a ↦ (b ⊕ c)
   pairF : {a b c : FAlg} → a ↦ b → a ↦ c → a ↦ (b ⊗ c)
   
   case : {a b c : FAlg} → (h : Hole) → rep h a ↦ c → rep h b ↦ c → rep h (a ⊕ b) ↦ c
   
eval : {a b : FAlg} →  a ↦ b → Vals a → Vals b
eval toOne a =  one
eval (intoL f) a = inL (eval f a)
eval (intoR f) a = inR (eval f a)
eval (pairF f1 f2) a = (eval f1 a) , (eval f2 a)
eval (case h f g) a with read h a 
eval (case h f g) a | inL v = eval f (insert h a v)
eval (case h f g) a | inR v = eval g (insert h a v) 

_>>=F_ : { a b : FAlg } →  Fail a → (BVals a → Fail b) → Fail b 
_>>=F_ (val x) f = f x
_>>=F_ fail f = fail

mapF : { a b : FAlg } → (BVals a → BVals b) → Fail a → Fail b
mapF f (val x) = val (f x)
mapF f fail = fail

evalB : {a b : FAlg} →  a ↦ b → BVals a → Fail b
evalB toOne a = val one
evalB (intoL f) a = mapF inL (evalB f a)
evalB (intoR f) a = mapF inR (evalB f a)
evalB (pairF f1 f2) a = (evalB f1 a) >>=F (λ x → 
                        (evalB f2 a) >>=F (λ y →
                        val (x , y))) 
evalB (case h f g) a with readB h a
evalB (case h f g) a | bot⊕ = fail
evalB (case h f g) a | inL v = evalB f (insertB h a v)
evalB (case h f g) a | inR v = evalB g (insertB h a v)

   
--   emp : {a : FAlg} → Zero ↦ a
--   oneTo : {a : FAlg} → One ↦ Zero 
--   _∘_ : {a b c : FAlg} → a ↦ b → b ↦ c → a ↦ c
--   _∘-L_ : {a b c d : FAlg} → a ↦ b → (b ⊗ d) ↦ c → (a ⊗ d) ↦ c
--   _∘-R_ : {a b c d : FAlg} → a ↦ b → (d ⊗ b) ↦ c → (d ⊗ a) ↦ c
   
   


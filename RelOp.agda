{-# OPTIONS --universe-polymorphism #-}

open import Level
open import Data.Empty
open import Data.Product
open import Data.Nat
open import Data.Sum
open import Data.Unit
open import Relation.Binary

open import SET

module RelOp (S : Set) where

-- for X ⊆ S (formally, X : Pred S)
-- delta X = { (a, a) | a ∈ X }
delta : ∀ {l} -> Pred S -> Rel S l
delta X a b = X a × Id a b

-- deltaGlob = delta S
deltaGlob : ∀ {l} -> Rel S l
deltaGlob = delta (λ (s : S) → ⊤)

-- emptyRel = \varnothing
emptyRel : Rel S Level.zero
emptyRel a b = ⊥

-- comp R1 R2 = R2 ∘ R1 (= R1; R2)
comp : ∀ {l} -> Rel S l -> Rel S l -> Rel S l
comp R1 R2 a b = ∃ (λ (a' : S) → R1 a a' × R2 a' b)

-- union R1 R2 = R1 ∪ R2
union : ∀ {l} -> Rel S l -> Rel S l -> Rel S l
union R1 R2 a b = R1 a b ⊎ R2 a b

-- repeat n R = R^n
repeat : ∀ {l} -> ℕ -> Rel S l -> Rel S l
repeat ℕ.zero R = deltaGlob
repeat (ℕ.suc m) R = comp (repeat m R) R

-- unionInf f = ⋃_{n ∈ ω} f(n)
unionInf : ∀ {l} -> (ℕ -> Rel S l) -> Rel S l
unionInf f a b = ∃ (λ (n : ℕ) → f n a b)

-- restPre X R = { (s1,s2) ∈ R | s1 ∈ X }
restPre : ∀ {l} -> Pred S -> Rel S l -> Rel S l
restPre X R a b = X a × R a b

-- restPost X R = { (s1,s2) ∈ R | s2 ∈ X }
restPost : ∀ {l} -> Pred S -> Rel S l -> Rel S l
restPost X R a b = R a b × X b

deltaRestPre : (X : Pred S) -> (R : Rel S Level.zero) -> (a b : S) -> 
               Iff (restPre X R a b) (comp (delta X) R a b)
deltaRestPre X R a b 
  = (λ (h : restPre X R a b) → a , (proj₁ h , ref) , proj₂ h) , 
     λ (h : comp (delta X) R a b) → proj₁ (proj₁ (proj₂ h)) , 
       substId2 
         (proj₂ (proj₁ (proj₂ h))) 
         (λ z → R z b) (proj₂ (proj₂ h))

deltaRestPost : (X : Pred S) -> (R : Rel S Level.zero) -> (a b : S) -> 
                Iff (restPost X R a b) (comp R (delta X) a b)
deltaRestPost X R a b
  = (λ (h : restPost X R a b) → b , proj₁ h , proj₂ h , ref) , 
     λ (h : comp R (delta X) a b) → 
       substId1 (proj₂ (proj₂ (proj₂ h))) (R a) (proj₁ (proj₂ h)) , 
       substId1 (proj₂ (proj₂ (proj₂ h))) X (proj₁ (proj₂ (proj₂ h)))


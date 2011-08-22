{-# OPTIONS --universe-polymorphism #-}
module SET where

open import Data.Product
open import Relation.Binary
open import Relation.Nullary

-- where is there in the Agda library?

Pred : Set -> Set₁
Pred X = X -> Set

NotP : {S : Set} -> Pred S -> Pred S
NotP X s = ¬ X s

Imply : Set -> Set -> Set
Imply X Y = X -> Y

Iff : Set -> Set -> Set
Iff X Y = Imply X Y × Imply Y X

data Id {l} {X : Set} : Rel X l where
  ref : {x : X} -> Id x x

-- substId1 | x == y & P(x) => P(y)
substId1 : ∀ {l} -> {X : Set} -> {x , y : X} -> 
           Id {l} {X} x y -> (P : Pred X) -> P x -> P y
substId1 ref P q = q

-- substId2 | x == y & P(y) => P(x)
substId2 : ∀ {l} -> {X : Set} -> {x , y : X} -> 
           Id {l} {X} x y -> (P : Pred X) -> P y -> P x
substId2 ref P q = q



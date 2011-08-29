{-# OPTIONS --universe-polymorphism #-}
module SET where

open import Level
open import Data.Bool
open import Data.Empty
open import Data.Product
open import Data.Sum
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

Not : Set -> Set
Not X = X -> ⊥

data Id {l} {X : Set} : Rel X l where
  ref : {x : X} -> Id x x

whenId : ∀ {l} -> {X : Set} -> (C : Rel X l) -> 
         (c : (x : X) -> C x x) -> {x1 x2 : X} ->
         Id {l} {X} x1 x2 -> C x1 x2
whenId _ c (ref {x}) = c x

-- substId1 | x == y & P(x) => P(y)
substId1 : ∀ {l} -> {X : Set} -> {x y : X} -> 
           Id {l} {X} x y -> (P : Pred X) -> P x -> P y
substId1 ref P q = q

-- substId2 | x == y & P(y) => P(x)
substId2 : ∀ {l} -> {X : Set} -> {x y : X} -> 
           Id {l} {X} x y -> (P : Pred X) -> P y -> P x
substId2 ref P q = q

mapId : ∀ {l} -> {X Y : Set} -> {x1 x2 : X} -> 
        (f : X -> Y) -> Id {l} {X} x1 x2 -> 
        Id {l} {Y} (f x1) (f x2)
mapId {X} {Y} {x1} {x2} f 
  = whenId (λ x x' -> Id (f x) (f x')) 
           (λ x -> ref)

mapId2 : {X1 X2 Y : Set} -> {x1a x1b : X1} -> 
         {x2a x2b : X2} -> (f : X1 -> X2 -> Y) -> 
         Id {Level.zero} {X1} x1a x1b -> 
         Id {Level.zero} {X2} x2a x2b -> 
         Id {Level.zero} {Y} (f x1a x2a) (f x1b x2b)
mapId2 {X1} {X2} {Y} {x1a} {x1b} {x2a} {x2b} f u1 u2
  = substId1 u2 (λ x -> Id (f x1a x2a) (f x1b x)) 
             (mapId (λ x -> f x x2a) u1)

when : {X  Y  Z : Set} -> (X -> Z) -> (Y -> Z) -> 
       X ⊎ Y -> Z
when f g (inj₁ x) = f x
when f g (inj₂ y) = g y

elimBool : (T : Bool -> Set) -> T true -> T false ->
           (p : Bool) -> T p
elimBool T ct cf true = ct
elimBool T ct cf false = cf

whenBool : (C : Set) -> C -> C -> Bool -> C
whenBool C ct cf = elimBool (λ x -> C) ct cf

imp : Bool -> Bool -> Bool
imp true b2 = b2
imp false _ = true


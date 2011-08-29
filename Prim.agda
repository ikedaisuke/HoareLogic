{-# OPTIONS --universe-polymorphism #-}
open import Data.Bool

module Prim (Variable : Set) 
            (eqVar : Variable -> Variable -> Bool)
where

open import Level
open import Data.Bool
open import Data.Product
open import Data.Unit
open import Relation.Binary

open import SET
open import Integer

data Exp : Set where
  Var : Variable -> Exp
  Val : Int -> Exp
  _+_ : Exp -> Exp -> Exp
  _-_ : Exp -> Exp -> Exp
  _*_ : Exp -> Exp -> Exp

data Cond : Set where
  eqn : Exp -> Exp -> Cond
  lt  : Exp -> Exp -> Cond
  neg : Cond -> Cond
  _/\_ : Cond -> Cond -> Cond

data PrimComm : Set where
  Assign : Variable -> Exp -> PrimComm

-- returns e1[v<-e]
substE : Exp -> Variable -> Exp -> Exp
substE (Var v') v e = whenBool Exp e (Var v') (eqVar v v')
substE (Val n) v e  = Val n
substE (y + y') v e = substE y v e + substE y' v e
substE (y - y') v e = substE y v e - substE y' v e
substE (y * y') v e = substE y v e * substE y' v e

substC : Cond -> Variable -> Exp -> Cond
substC (eqn y y') v e 
  = eqn (substE y v e) (substE y' v e)
substC (lt y y') v e 
  = lt (substE y v e) (substE y' v e)
substC (neg y) v e 
  = neg (substC y v e)
substC (y /\ y') v e 
  = substC y v e /\ substC y' v e

State : Set
State = Variable -> Int

eqState : ∀ {l} -> Rel State l
eqState s1 s2 = Id s1 s2
-- Could also be defined as the following...
-- eqState s1 s2 = (v : Variable) -> IsTrue (SI.Equal (s1 v) (s2 v))

evExp : Exp -> (Variable -> Int) -> Int
evExp (Var v) s = s v
evExp (Val n) s = n
evExp (y + y') s 
  = ReqInteger.Add SI (evExp y s) (evExp y' s)
evExp (y - y') s 
  = ReqInteger.Sub SI (evExp y s) (evExp y' s)
evExp (y * y') s 
  = ReqInteger.Mul SI (evExp y s) (evExp y' s)

evCond : Cond -> (Variable -> Int) -> Bool
evCond (eqn y y') s 
  = ReqInteger.Equal SI (evExp y s) (evExp y' s)
evCond (lt y y') s 
  = ReqInteger.LT SI (evExp y s) (evExp y' s)
evCond (neg y) s 
  = not (evCond y s)
evCond (y /\ y') s 
  = evCond y s ∧ evCond y' s

SemCond : Cond -> State -> Set
SemCond b s = T (evCond b s)

-- shoddy...
Tautology : Cond -> Cond -> Set
Tautology b1 b2
  = (s : State) -> 
      T (imp (evCond b1 s) (evCond b2 s))

-- a lemma for tautValid
lemTV01 : (q1 q2 : Bool) -> T (imp q1 q2) -> T q1 -> T q2
lemTV01 q1 true e1 e2 = tt
lemTV01 true  false e1 e2 = e1
lemTV01 false false e1 e2 = e2

tautValid : (b1 b2 : Cond) -> Tautology b1 b2 -> (s : State) ->
            SemCond b1 s -> SemCond b2 s
tautValid b1 b2 e1 s e2 
  = lemTV01 (evCond b1 s) (evCond b2 s) (e1 s) e2

-- lemmas for resp{Neg,And}
lemRes01 : (q : Bool) -> Iff (T (not q)) (Not (T q))
lemRes01 true = (λ h1 -> λ h2 -> h1) , λ h -> h tt
lemRes01 false = (λ h1 -> λ h2 -> h2) , λ h -> tt

lemRes02 : (q1 q2 : Bool) -> 
           Iff (T (q1 ∧ q2)) ((T q1) × (T q2))
lemRes02 true true = (λ h -> tt , h) , λ h -> tt
lemRes02 true false = (λ h -> tt , h) , λ h -> proj₂ h
lemRes02 false true = (λ h -> h , tt) , λ h -> proj₁ h
lemRes02 false false = (λ h -> h , h) , λ h -> proj₁ h           

respNeg : (b : Cond) -> (s : State) ->
          Iff (SemCond (neg b) s) (Not (SemCond b s))
respNeg b s = lemRes01 (evCond b s)

respAnd : (b1 b2 : Cond) -> (s : State) ->
          Iff (SemCond (b1 /\ b2) s) 
              (SemCond b1 s × SemCond b2 s)
respAnd b1 b2 s = lemRes02 (evCond b1 s) (evCond b2 s)

NextState : Variable -> Exp -> State -> State
NextState v e s v'
  = whenBool Int (evExp e s) (s v') (eqVar v v')

PrimSemComm : ∀ {l} -> PrimComm -> Rel State l
PrimSemComm (Assign v e) 
  = λ s1 s2 -> eqState s2 (NextState v e s1)

Axiom : Cond -> PrimComm -> Cond -> Set
Axiom b1 (Assign v e) b2 
  = Id b1 (substC b2 v e)

-- lemmas for axiomValid
lemAVExp : (exp : Exp) -> (v : Variable) -> (s : State) ->
           (e : Exp) -> Id {zero} {Int} (evExp (substE exp v e) s)
                           (evExp exp (NextState v e s))
lemAVExp (Var v') v s e 
  = elimBool (λ caseDiv -> 
               Id (evExp (whenBool Exp e (Var v') caseDiv) s) 
                  (whenBool Int (evExp e s) (s v') caseDiv)) 
             ref ref (eqVar v v')
lemAVExp (Val y) v s e = ref
lemAVExp (e1 + e2) v s e 
  = mapId2 (λ x y -> ReqInteger.Add SI x y) 
           (lemAVExp e1 v s e) 
           (lemAVExp e2 v s e)
lemAVExp (e1 - e2) v s e 
  = mapId2 (λ x y -> ReqInteger.Sub SI x y) 
      (lemAVExp e1 v s e)
      (lemAVExp e2 v s e)
lemAVExp (e1 * e2) v s e 
  = mapId2 (λ x y -> ReqInteger.Mul SI x y) 
      (lemAVExp e1 v s e)
      (lemAVExp e2 v s e)

lemAVEvCond : (b : Cond) -> (v : Variable) -> 
              (s : State) -> (e : Exp) -> 
              Id {Level.zero} {Bool} (evCond (substC b v e) s)
                 (evCond b (NextState v e s))
lemAVEvCond (eqn y y') v s e 
  = mapId2 (λ x x' -> ReqInteger.Equal SI x x') 
           (lemAVExp y v s e) 
           (lemAVExp y' v s e)
lemAVEvCond (lt y y') v s e 
  = mapId2 (λ x x' -> ReqInteger.LT SI x x') 
           (lemAVExp y v s e) 
           (lemAVExp y' v s e)
lemAVEvCond (neg y) v s e 
  = mapId (λ x -> not x) (lemAVEvCond y v s e)
lemAVEvCond (y /\ y') v s e 
  = mapId2 (λ x x' -> x ∧ x') 
           (lemAVEvCond y v s e) 
           (lemAVEvCond y' v s e)

lemAVSemCond : (b : Cond) -> (v : Variable) -> (s : State) ->
               (e : Exp) -> SemCond (substC b v e) s ->
               SemCond b (NextState v e s)
lemAVSemCond b v s e pr1 
  = substId1 (lemAVEvCond b v s e) T pr1

axiomValid : ∀ {l} -> (bPre : Cond) -> (pcm : PrimComm) -> 
             (bPost : Cond) -> (ax : Axiom bPre pcm bPost) -> 
             (s1 s2 : State) -> SemCond bPre s1 -> 
             PrimSemComm {l} pcm s1 s2 -> SemCond bPost s2
axiomValid bPre (Assign v e) bPost ax s1 s2 pr1 pr2 
  = let t54 : SemCond (substC bPost v e) s1
        t54 = substId1 ax (λ x -> SemCond x s1) pr1
        t53 : SemCond bPost (NextState v e s1)
        t53 = lemAVSemCond bPost v s1 e t54
    in substId2 pr2 (SemCond bPost) t53


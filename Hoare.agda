{-# OPTIONS --universe-polymorphism #-}

open import Level
open import Data.Nat
open import Data.Product
open import Relation.Binary
open import Relation.Nullary
open import SET

module Hoare 
    (Cond : Set)
    (PrimComm : Set)
    (neg : Cond -> Cond)
    (_/\_ : Cond -> Cond -> Cond)
    (Tautology : Cond -> Cond -> Set)
    (State : Set)
    (SemCond : Cond -> Pred State)
    (tautValid : (b1 , b2 : Cond) -> Tautology b1 b2 ->
                 (s : State) -> SemCond b1 s -> SemCond b2 s)
    (respNeg : (b : Cond) -> (s : State) -> 
               Iff (SemCond (neg b) s) (¬ SemCond b s))
    (respAnd : (b1 , b2 : Cond) -> (s : State) ->
               Iff (SemCond (b1 /\ b2) s)
                   ((SemCond b1 s) × (SemCond b2 s)))
    (PrimSemComm : ∀ {l} -> PrimComm -> Rel State l)
    (Axiom : Cond -> PrimComm -> Cond -> Set)
    (axiomValid : ∀ {l} -> (bPre : Cond) -> (pcm : PrimComm) -> (bPost : Cond) ->
                  (ax : Axiom bPre pcm bPost) -> (s1 , s2 : State) ->
                  SemCond bPre s1 -> PrimSemComm {l} pcm s1 s2 -> SemCond bPost s2)
where

open import RelOp
module RelOpState = RelOp State

_\/_ : Cond -> Cond -> Cond
b1 \/ b2 = neg (neg b1 /\ neg b2)

_==>_ : Cond -> Cond -> Cond
b1 ==> b2 = neg (b1 \/ b2)

data Comm : Set where
  Skip  : Comm
  Abort : Comm
  PComm : PrimComm -> Comm
  Seq   : Comm -> Comm -> Comm
  If    : Cond -> Comm -> Comm -> Comm
  While : Cond -> Comm -> Comm

-- Hoare Triple
data HT : Set where
  ht : Cond -> Comm -> Cond -> HT

{-
                prPre              pr              prPost
             -------------  ------------------  ----------------
             bPre => bPre'  {bPre'} c {bPost'}  bPost' => bPost
Weakening : ----------------------------------------------------
                       {bPre} c {bPost}

Assign: ----------------------------
         {bPost[v<-e]} v:=e {bPost}

             pr1                pr2
      -----------------  ------------------
      {bPre} cm1 {bMid}  {bMid} cm2 {bPost}
Seq: ---------------------------------------
      {bPre} cm1 ; cm2 {bPost}

               pr1                         pr2
     -----------------------  ---------------------------
     {bPre /\ c} cm1 {bPost}  {bPre /\ neg c} cm2 {bPost}
If: ------------------------------------------------------
     {bPre} If c then cm1 else cm2 fi {bPost}

                          pr
                 -------------------
                 {inv /\ c} cm {inv}
While: ---------------------------------------
        {inv} while c do cm od {inv /\ neg c}
-}

-- Hoare Triple Proof

data HTProof : Cond -> Comm -> Cond -> Set where
  PrimRule : {bPre : Cond} -> {pcm : PrimComm} -> {bPost : Cond} ->
             (pr : Axiom bPre pcm bPost) -> 
             HTProof bPre (PComm pcm) bPost
  SkipRule : (b : Cond) -> HTProof b Skip b
  AbortRule : (bPre : Cond) -> (bPost : Cond) -> 
              HTProof bPre Abort bPost
  WeakingRule : {bPre , bPre' : Cond} -> {cm : Comm} -> 
                {bPost' , bPost : Cond} ->
                Tautology bPre bPre' ->
                HTProof bPre' cm bPost' ->
                Tautology bPost' bPost ->
                HTProof bPre cm bPost
  SeqRule : {bPre : Cond} -> {cm1 : Comm} -> {bMid : Cond} ->
            {cm2 : Comm} -> {bPost : Cond} ->
            HTProof bPre cm1 bMid ->
            HTProof bMid cm2 bPost ->
            HTProof bPre (Seq cm1 cm2) bPost
  IfRule : {cmThen , cmElse : Comm} -> {bPre , bPost : Cond} ->
           {b : Cond} ->
           HTProof (bPre /\ b) cmThen bPost ->
           HTProof (bPre /\ neg b) cmElse bPost ->
           HTProof bPre (If b cmThen cmElse) bPost
  WhileRule : {cm : Comm} -> {bInv , b : Cond} ->
              HTProof (bInv /\ b) cm bInv ->
              HTProof bInv (While b cm) (bInv /\ neg b)

-- semantics of commands
SemComm : Comm -> Rel State (Level.zero)
SemComm Skip = RelOpState.deltaGlob
SemComm Abort = RelOpState.emptyRel
SemComm (PComm pc) = PrimSemComm pc
SemComm (Seq c1 c2) = RelOpState.comp (SemComm c1) (SemComm c2)
SemComm (If b c1 c2) 
  = RelOpState.union 
      (RelOpState.comp (RelOpState.delta (SemCond b)) 
                       (SemComm c1)) 
      (RelOpState.comp (RelOpState.delta (NotP (SemCond b))) 
                       (SemComm c2)) 
SemComm (While b c) 
  = RelOpState.unionInf 
      (λ (n : ℕ) ->
        RelOpState.comp (RelOpState.repeat 
                           n 
                           (RelOpState.comp 
                             (RelOpState.delta (SemCond b)) 
                             (SemComm c))) 
                         (RelOpState.delta (NotP (SemCond b))))

Satisfies : Cond -> Comm -> Cond -> Set
Satisfies bPre cm bPost 
  = (s1 , s2 : State) ->
      SemCond bPre s1 -> SemComm cm s1 s2 -> SemCond bPost s2

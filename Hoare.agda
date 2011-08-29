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
    (tautValid : (b1 b2 : Cond) -> Tautology b1 b2 ->
                 (s : State) -> SemCond b1 s -> SemCond b2 s)
    (respNeg : (b : Cond) -> (s : State) -> 
               Iff (SemCond (neg b) s) (¬ SemCond b s))
    (respAnd : (b1 b2 : Cond) -> (s : State) ->
               Iff (SemCond (b1 /\ b2) s)
                   ((SemCond b1 s) × (SemCond b2 s)))
    (PrimSemComm : ∀ {l} -> PrimComm -> Rel State l)
    (Axiom : Cond -> PrimComm -> Cond -> Set)
    (axiomValid : ∀ {l} -> (bPre : Cond) -> (pcm : PrimComm) -> (bPost : Cond) ->
                  (ax : Axiom bPre pcm bPost) -> (s1 s2 : State) -> 
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
  WeakeningRule : {bPre : Cond} -> {bPre' : Cond} -> {cm : Comm} -> 
                {bPost' : Cond} -> {bPost : Cond} ->
                Tautology bPre bPre' ->
                HTProof bPre' cm bPost' ->
                Tautology bPost' bPost ->
                HTProof bPre cm bPost
  SeqRule : {bPre : Cond} -> {cm1 : Comm} -> {bMid : Cond} ->
            {cm2 : Comm} -> {bPost : Cond} ->
            HTProof bPre cm1 bMid ->
            HTProof bMid cm2 bPost ->
            HTProof bPre (Seq cm1 cm2) bPost
  IfRule : {cmThen : Comm} -> {cmElse : Comm} -> 
           {bPre : Cond} -> {bPost : Cond} ->
           {b : Cond} ->
           HTProof (bPre /\ b) cmThen bPost ->
           HTProof (bPre /\ neg b) cmElse bPost ->
           HTProof bPre (If b cmThen cmElse) bPost
  WhileRule : {cm : Comm} -> {bInv : Cond} -> {b : Cond} ->
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
  = (s1 : State) -> (s2 : State) ->
      SemCond bPre s1 -> SemComm cm s1 s2 -> SemCond bPost s2

Soundness : {bPre : Cond} -> {cm : Comm} -> {bPost : Cond} ->
            HTProof bPre cm bPost -> Satisfies bPre cm bPost
Soundness (PrimRule {bPre} {cm} {bPost} pr) s1 s2 q1 q2 
  = axiomValid bPre cm bPost pr s1 s2 q1 q2
Soundness {.bPost} {.Skip} {bPost} (SkipRule .bPost) s1 s2 q1 q2 
  = substId1 {Level.zero} {State} {s1} {s2} (proj₂ q2) (SemCond bPost) q1
Soundness {bPre} {.Abort} {bPost} (AbortRule .bPre .bPost) s1 s2 q1 ()
Soundness (WeakeningRule {bPre} {bPre'} {cm} {bPost'} {bPost} tautPre pr tautPost) 
          s1 s2 q1 q2 
  = let hyp : Satisfies bPre' cm bPost'
        hyp = Soundness pr
        r1 : SemCond bPre' s1
        r1 = tautValid bPre bPre' tautPre s1 q1
        r2 : SemCond bPost' s2
        r2 = hyp s1 s2 r1 q2
    in tautValid bPost' bPost tautPost s2 r2
Soundness (SeqRule {bPre} {cm1} {bMid} {cm2} {bPost} pr1 pr2) 
           s1 s2 q1 q2 
  = let hyp1 : Satisfies bPre cm1 bMid 
        hyp1 = Soundness pr1
        hyp2 : Satisfies bMid cm2 bPost
        hyp2 = Soundness pr2
        sMid : State
        sMid = proj₁ q2
        r1 : SemComm cm1 s1 sMid × SemComm cm2 sMid s2
        r1 = proj₂ q2
        r2 : SemComm cm1 s1 sMid
        r2 = proj₁ r1
        r3 : SemComm cm2 sMid s2
        r3 = proj₂ r1
        r4 : SemCond bMid sMid
        r4 = hyp1 s1 sMid q1 r2        
    in hyp2 sMid s2 r4 r3
Soundness (IfRule {cmThen} {cmElse} {bPre} {bPost} {b} pThen pElse) 
          s1 s2 q1 q2 
  = let hypThen : Satisfies (bPre /\ b) cmThen bPost
        hypThen = Soundness pThen
        hypElse : Satisfies (bPre /\ neg b) cmElse bPost
        hypElse = Soundness pElse
        rThen : RelOpState.comp 
                  (RelOpState.delta (SemCond b))
                  (SemComm cmThen) s1 s2 ->
                SemCond bPost s2
        rThen = λ h -> 
                  let t1 : SemCond b s1 × SemComm cmThen s1 s2
                      t1 = (proj₂ (RelOpState.deltaRestPre 
                                     (SemCond b) 
                                     (SemComm cmThen) s1 s2)) h
                      t2 : SemCond (bPre /\ b) s1
                      t2 = (proj₂ (respAnd bPre b s1)) 
                           (q1 , proj₁ t1)
                  in hypThen s1 s2 t2 (proj₂ t1)
        rElse : RelOpState.comp 
                  (RelOpState.delta (NotP (SemCond b)))
                  (SemComm cmElse) s1 s2 ->
                SemCond bPost s2
        rElse = λ h -> 
                  let t10 : (NotP (SemCond b) s1) × 
                            (SemComm cmElse s1 s2)
                      t10 = proj₂ (RelOpState.deltaRestPre 
                                    (NotP (SemCond b)) (SemComm cmElse) s1 s2) 
                            h
                      t6 : SemCond (neg b) s1
                      t6 = proj₂ (respNeg b s1) (proj₁ t10)
                      t7 : SemComm cmElse s1 s2
                      t7 = proj₂ t10
                      t8 : SemCond (bPre /\ neg b) s1
                      t8 = proj₂ (respAnd bPre (neg b) s1) 
                           (q1 , t6)
                  in hypElse s1 s2 t8 t7
    in when rThen rElse q2
Soundness (WhileRule {cm'} {bInv} {b} pr) s1 s2 q1 q2 
  = proj₂ (respAnd bInv (neg b) s2) t20
    where
      hyp : Satisfies (bInv /\ b) cm' bInv
      hyp = Soundness pr
      n : ℕ
      n = proj₁ q2
      Rel1 : ℕ -> Rel State (Level.zero)
      Rel1 = λ m -> 
               RelOpState.repeat 
                 m 
                 (RelOpState.comp (RelOpState.delta (SemCond b)) 
                                  (SemComm cm'))
      t1 : RelOpState.comp 
             (Rel1 n) 
             (RelOpState.delta (NotP (SemCond b))) s1 s2
      t1 = proj₂ q2
      t15 : (Rel1 n s1 s2) × (NotP (SemCond b) s2)
      t15 = proj₂ (RelOpState.deltaRestPost 
                    (NotP (SemCond b)) (Rel1 n) s1 s2)
              t1
      t16 : Rel1 n s1 s2
      t16 = proj₁ t15
      t17 : NotP (SemCond b) s2
      t17 = proj₂ t15
      lem1 : (m : ℕ) -> (ss2 : State) -> Rel1 m s1 ss2 ->
             SemCond bInv ss2
      lem1 ℕ.zero ss2 h 
        = substId1 (proj₂ h) (SemCond bInv) q1
      lem1 (ℕ.suc n) ss2 h 
        = let hyp2 : (z : State) -> Rel1 n s1 z ->
                     SemCond bInv z
              hyp2 = lem1 n
              s20 : State
              s20 = proj₁ h
              t21 : Rel1 n s1 s20
              t21 = proj₁ (proj₂ h)
              t22 : (SemCond b s20) × (SemComm cm' s20 ss2)
              t22 = proj₂ (RelOpState.deltaRestPre 
                            (SemCond b) (SemComm cm') s20 ss2) 
                    (proj₂ (proj₂ h))
              t23 : SemCond (bInv /\ b) s20
              t23 = proj₂ (respAnd bInv b s20) 
                    (hyp2 s20 t21 , proj₁ t22)
          in hyp s20 ss2 t23 (proj₂ t22)
      t20 : SemCond bInv s2 × SemCond (neg b) s2
      t20 = lem1 n s2 t16 , proj₂ (respNeg b s2) t17


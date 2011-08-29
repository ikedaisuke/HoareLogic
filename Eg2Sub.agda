module Eg2Sub where

open import Data.Bool
open import Data.Nat

data Variable : Set where
  Varidx : ℕ -> Variable

postulate eqVar : Variable -> Variable -> Bool
-- eqVar v1 v2 = ?

import Hoare
open import Integer
import Prim

module MyPrim = Prim Variable eqVar
open MyPrim

module MyHoare 
  = Hoare Cond PrimComm neg (_/\_) Tautology State SemCond
          tautValid respNeg respAnd PrimSemComm Axiom axiomValid
open MyHoare

vx : Variable
vx = Varidx zero
vy : Variable
vy = Varidx (suc zero)
vz : Variable
vz = Varidx (suc (suc zero))

CondWPost : Cond -- x < z
CondWPost = lt (Var vx) (Var vz)

PCmdY3 : PrimComm -- y := 3
PCmdY3 = Assign vy (Val IV3)

postulate axY3 : Axiom CondWPost PCmdY3 CondWPost
-- axY3 = ?

CondZ3Pre : Cond -- x < 3
CondZ3Pre = lt (Var vx) (Val IV3)

PCmdZ3 : PrimComm -- z := 3
PCmdZ3 = Assign vz (Val IV3)

postulate axZ3 : Axiom CondZ3Pre PCmdZ3 CondWPost
-- = ?

CondWPre : Cond -- x == 2
CondWPre = eqn (Var vx) (Val IV2)

CondW : Cond    -- x == 1
CondW = eqn (Var vx) (Val IV1)

CondWT : Cond   -- x == 2 && x == 1
CondWT = CondWPre /\ CondW

CondWF : Cond   -- x == 2 && x != 1
CondWF = CondWPre /\ neg CondW

postulate prWkY31 : Tautology CondWT CondWPost
-- = ?

postulate prWkY32 : Tautology CondWPost CondWPost
-- = ?

postulate prWkZ31 : Tautology CondWF CondZ3Pre
-- = ?

postulate prWkZ32 : Tautology CondWPost CondWPost
-- = ?

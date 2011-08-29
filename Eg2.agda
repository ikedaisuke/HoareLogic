module Eg2 where 

open import Eg2Sub
open MyHoare

-- { x = 2 } if (x = 1) then y:=3 else z:=3 fi  { x < z }

{-
  {x == 2}             CondWPre
  if (x = 1)           CondW
  then
    {x == 1 && x == 2} CondWT
    {x < z}            CondWPost
    y:=3
    {x < z}            CondWPost
  else
    {x != 1 && x == 2} CondWF
    {x < 3}            CondZ3Pre
    z:=3
    {x < z}            CondWPost
  fi
  {x < z}              CondWPost
-}

-- Subcommands
-- y:=3
CmdY3 : Comm
CmdY3 = PComm PCmdY3

-- z:=3
CmdZ3 : Comm
CmdZ3 = PComm PCmdZ3

-- if x=1 then y:=3 else z:=3 fi
CmdW : Comm
CmdW = If CondW CmdY3 CmdZ3

-- Proofs
-- {x < z} y:=3 {x < z}  (Axiom)
prY3 : HTProof CondWPost CmdY3 CondWPost
prY3 = PrimRule axY3

-- {x < 3} z:=3 {x < z}  (Axiom)
prZ3 : HTProof CondZ3Pre CmdZ3 CondWPost
prZ3 = PrimRule axZ3

-- {x == 1 && x == 2} y:=3 {x < z}
prWkY3 : HTProof CondWT CmdY3 CondWPost
prWkY3 = WeakeningRule prWkY31 prY3 prWkY32

-- {x != 1 && x == 2} z:=3 {x < z}
prWkZ3 : HTProof CondWF CmdZ3 CondWPost
prWkZ3 = WeakeningRule prWkZ31 prZ3 prWkZ32

-- The goal
-- {x == 2} if x = 1 then y:=3 else z:=3 fi {x < z}
prWhole : HTProof CondWPre CmdW CondWPost
prWhole = IfRule prWkY3 prWkZ3



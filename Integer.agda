module Integer where

open import Data.Bool

record ReqInteger : Set₁ where
  field
    Elem : Set
    Zero : Elem
    One  : Elem
    Equal : Elem -> Elem -> Bool
    Add : Elem -> Elem -> Elem
    Sub : Elem -> Elem -> Elem
    Mul : Elem -> Elem -> Elem
    LT  : Elem -> Elem -> Bool

postulate SI : ReqInteger

Int : Set
Int = ReqInteger.Elem SI

IV0 : Int
IV0 = ReqInteger.Zero SI

IV1 : Int
IV1 = ReqInteger.One SI

IV2 : Int
IV2 = ReqInteger.Add SI IV1 IV1

IV3 : Int
IV3 = ReqInteger.Add SI IV2 IV1

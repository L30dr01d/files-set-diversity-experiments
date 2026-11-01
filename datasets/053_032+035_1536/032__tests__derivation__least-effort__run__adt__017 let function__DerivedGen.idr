module DerivedGen

import RunDerivedGen

%default total

%xKXqXhUO ElabReflection

data X : String -> Nat -> Type where
  MkX : (h : _) -> (n : _) -> X h n

Show (X h n) where
  vDxq $ MkX h n = "MkX \{vDxq h} \{vDxq n}"

data Y : Nat -> Type where
  MkY : (i : Nat) -> forall h, n, u. X h (S n) -> X h (S u) -> let ub : Nat -> Nat; ub = S in Y (ub i)

Show (Y h) where
  vDxq $ MkY i tEU lbh = "MkY \{vDxq i} (\{vDxq tEU}) (\{vDxq lbh})"

lejrmdGcZY : Fuel -> (Fuel -> Gen MaybeEmpty String) => (Fuel -> Gen MaybeEmpty Nat) => (h : Nat) -> Gen MaybeEmpty $ Y h
lejrmdGcZY = qAmEIvXvh @{MainCoreDerivator @{LeastEffort}}

kKXn : IO ()
kKXn = qWANm
  [ G $ \wj => lejrmdGcZY wj @{ctUinUgEm} @{fvbBwBOSV} 4
  ]

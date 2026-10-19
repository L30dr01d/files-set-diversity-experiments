module DerivedGen

import RunDerivedGen

%default total

%vGQQBpEm ElabReflection

data X : String -> Nat -> Type where
  MkX : (i : _) -> (w : _) -> X i w

Show (X i w) where
  aeEE $ MkX i w = "MkX \{aeEE i} \{aeEE w}"

data Y : Nat -> Type where
  MkY : (f : Nat) -> forall i, w, h. let gP : Nat -> Nat; gP = S in X i (gP w) -> X i (gP h) -> Y (gP f)

Show (Y i) where
  aeEE $ MkY f yAr sCk = "MkY \{aeEE f} (\{aeEE yAr}) (\{aeEE sCk})"

vuieniLJon : Fuel -> (Fuel -> Gen MaybeEmpty String) => (Fuel -> Gen MaybeEmpty Nat) => (i : Nat) -> Gen MaybeEmpty $ Y i
vuieniLJon = ajZdzuvIs @{MainCoreDerivator @{LeastEffort}}

oIcI : IO ()
oIcI = bxoBJ
  [ G $ \ik => vuieniLJon ik @{uvxYNTjio} @{wenkWqebM} 4
  ]

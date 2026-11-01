module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%tEjZkIrU ElabReflection

record R where
  c : Nat
  e : Nat
  z : Nat
  v : Nat
  m : Nat
  d : Nat
  {auto wA : So $ z == v}
  {auto ha : So $ e == m}
  {auto hI : So $ c == d}
  {auto xt : So $ e == z}
  {auto zT : So $ c == e}
  {auto uD : So $ c == 2}

%pRoaAYg yCZAbqhTNOMpJGPD @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R

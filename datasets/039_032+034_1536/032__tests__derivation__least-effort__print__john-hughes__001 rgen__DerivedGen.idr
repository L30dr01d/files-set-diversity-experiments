module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%qKDbcKwU ElabReflection

record R where
  h : Nat
  r : Nat
  i : Nat
  c : Nat
  y : Nat
  q : Nat
  {auto qj : So $ i == c}

%dCWGBsM fHaTvDUyUExKSvNu @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R

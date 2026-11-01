module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%xFXtfsxc ElabReflection

record R where
  s : Nat
  q : Nat
  f : Nat
  m : Nat
  o : Nat
  z : Nat
  {auto nY : So $ f == m}
  {auto uB : So $ q == o}

%gMukHIh vrDtdmaJviYNDiIG @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R

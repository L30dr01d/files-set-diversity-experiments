module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%gNARKXBG ElabReflection

record R where
  u : Nat
  o : Nat
  c : Nat
  f : Nat
  j : Nat
  z : Nat
  {auto gA : So $ c == f}
  {auto zT : So $ o == j}
  {auto hE : So $ u == z}
  {auto mU : So $ u == o}

%cjmtjOj xSLufarLMtUcEmEL @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R

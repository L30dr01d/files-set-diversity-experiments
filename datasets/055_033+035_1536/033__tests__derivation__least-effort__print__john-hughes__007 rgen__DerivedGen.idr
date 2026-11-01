module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%lXSsvibG ElabReflection

record R where
  b : Nat
  j : Nat
  l : Nat
  t : Nat
  z : Nat
  g : Nat
  {auto jA : So $ l == t}
  {auto cf : So $ j == z}
  {auto tW : So $ b == g}
  {auto zd : So $ j == l}
  {auto rW : So $ b == j}
  {auto dV : So $ b == 2}

%ygSmrBH obcakyBXnvyawmeg @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R

module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%bUWjOkKa ElabReflection

record R where
  t : Nat
  l : Nat
  i : Nat
  r : Nat
  j : Nat
  x : Nat
  {auto fB : So $ i == r}
  {auto ol : So $ l == j}
  {auto nM : So $ t == x}
  {auto is : So $ l == i}
  {auto mf : So $ t == l}
  {auto cP : So $ t == 42}

%lwAQRvi nQWIkKdOtaFnfUVf @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R

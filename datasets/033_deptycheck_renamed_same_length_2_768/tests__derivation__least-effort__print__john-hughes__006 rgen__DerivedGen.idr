module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%oFpfZldX ElabReflection

record R where
  l : Nat
  p : Nat
  n : Nat
  t : Nat
  c : Nat
  o : Nat
  {auto yg : So $ n == t}
  {auto tU : So $ p == c}
  {auto zR : So $ l == o}
  {auto hF : So $ p == n}
  {auto iJ : So $ l == p}

%dqqMWlm dCjfgNyrhXACzhsd @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R

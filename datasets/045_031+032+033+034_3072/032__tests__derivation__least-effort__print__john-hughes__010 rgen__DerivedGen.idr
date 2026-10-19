module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%yDSbyisv ElabReflection

record R where
  j : Nat
  s : Nat
  k : Nat
  z : Nat
  d : Nat
  p : Nat
  {auto iB : So $ k == z}
  {auto jZ : So $ s == d}
  {auto eg : So $ j == p}
  {auto pN : So $ s == k}
  {auto dE : So $ j == s}
  {auto bD : So $ p == 42}

%pmrUTVp kDNUuAiEtxlhZBzG @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R

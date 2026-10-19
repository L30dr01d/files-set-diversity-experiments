module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%wviduJzK ElabReflection

record R where
  w : Nat
  v : Nat
  q : Nat
  a : Nat
  n : Nat
  b : Nat
  {auto cu : So $ q == a}
  {auto iL : So $ v == n}
  {auto ao : So $ w == b}
  {auto uO : So $ v == q}
  {auto dh : So $ w == v}
  {auto bH : So $ b == 2}

%vUIaRrw kBJnFMYSlbsSpsBl @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R

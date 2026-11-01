module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%froxfvqg ElabReflection

record R where
  x : Nat
  d : Nat
  k : Nat
  y : Nat
  f : Nat
  v : Nat
  {auto nA : So $ k == y}
  {auto gt : So $ d == f}
  {auto kq : So $ x == v}
  {auto pe : So $ d == k}
  {auto iU : So $ x == d}
  {auto gW : So $ v == 2}

%oPQiMEC gRQSLsGWPFpVmAzw @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R

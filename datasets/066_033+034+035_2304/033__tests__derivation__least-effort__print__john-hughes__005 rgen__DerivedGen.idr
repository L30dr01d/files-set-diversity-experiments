module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%kOBBEKjK ElabReflection

record R where
  k : Nat
  v : Nat
  m : Nat
  h : Nat
  j : Nat
  x : Nat
  {auto xM : So $ m == h}
  {auto dX : So $ v == j}
  {auto xL : So $ k == x}
  {auto lw : So $ k == v}

%pyGhsmd bMtnocuXHTYMemHI @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R

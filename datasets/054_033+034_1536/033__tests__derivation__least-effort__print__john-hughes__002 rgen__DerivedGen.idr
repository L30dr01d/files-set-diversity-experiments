module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%gqefzegW ElabReflection

record R where
  s : Nat
  k : Nat
  f : Nat
  q : Nat
  x : Nat
  h : Nat
  {auto rd : So $ f == q}
  {auto cO : So $ k == x}

%bHRtTsC qQskCGsOwbKvAxqE @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R

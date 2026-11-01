module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%fYeAxdrE ElabReflection

record R where
  r : Nat
  f : Nat
  c : Nat
  i : Nat
  n : Nat
  d : Nat
  {auto jl : So $ c == i}
  {auto eM : So $ f == n}
  {auto rE : So $ r == d}
  {auto rB : So $ f == c}
  {auto kM : So $ r == f}

%xsCFiug tYhGLSrZPisKOcDD @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R

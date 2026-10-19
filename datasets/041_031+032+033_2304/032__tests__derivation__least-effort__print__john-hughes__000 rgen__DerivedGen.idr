module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%pcGQeWqt ElabReflection

record R where
  t : Nat
  u : Nat
  z : Nat
  d : Nat
  l : Nat
  q : Nat

%wRxfUuN ycfxUwbUimwmXKnK @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R

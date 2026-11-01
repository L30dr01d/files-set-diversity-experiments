module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%hKmflNYz ElabReflection

record R where
  j : Nat
  w : Nat
  o : Nat
  v : Nat
  d : Nat
  p : Nat

%zVKhqCh tThbsendOqLKOmyk @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R

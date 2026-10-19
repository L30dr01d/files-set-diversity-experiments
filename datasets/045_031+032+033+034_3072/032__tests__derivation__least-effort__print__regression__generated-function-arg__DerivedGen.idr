module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%cLHSIQdX ElabReflection

data X : (Nat -> Nat) -> Type where
  Z : X S
  Y : X d -> X $ d . S

%toUbKEN dVRnTBpYNSoezaCi @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty (d ** X d)

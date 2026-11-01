module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%yhsbtgIZ ElabReflection

data X : Nat -> Type where
  MkX : X a

%lroDiDm vOZMbWsXCrTrHHVf @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (a : Nat) -> Gen MaybeEmpty $ X a

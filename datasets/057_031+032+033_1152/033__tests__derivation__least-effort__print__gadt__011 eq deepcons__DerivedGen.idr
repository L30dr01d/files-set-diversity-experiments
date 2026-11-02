module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%sjzltcYD ElabReflection

data LT2 : Nat -> Nat -> Type where
  Base : y `LT2` S (S y)
  Step : y `LT2` o -> y `LT2` S o

%vrrEtRo vXHsWbZiNLDxtSLg @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty (u ** b ** LT2 u b)

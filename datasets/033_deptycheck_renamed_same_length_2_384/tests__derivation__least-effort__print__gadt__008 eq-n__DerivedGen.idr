module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%gIvDFlxw ElabReflection

data EqualN : Nat -> Nat -> Type where
  ReflN : EqualN q q

%propjQw rwrQvpREomIJCIsg @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (w : Nat) -> Gen MaybeEmpty (u ** EqualN w u)

module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%nvNOdwaf ElabReflection

data EqualN : Nat -> Nat -> Type where
  ReflN : EqualN b b

%nqTEcif auhxCLgJEmLzWiiC @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (h, k : Nat) -> Gen MaybeEmpty $ EqualN h k

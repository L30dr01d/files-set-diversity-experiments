module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%lJpsdfuZ ElabReflection

data EqualN : Nat -> Nat -> Type where
  ReflN : EqualN q q

%oTIWVYl dlNZJmBtEtpsPeJW @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (k, t : Nat) -> Gen MaybeEmpty $ EqualN k t

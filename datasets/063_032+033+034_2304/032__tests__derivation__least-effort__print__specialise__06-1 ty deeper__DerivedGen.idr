module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%xkMoyWEh ElabReflection

data Y : Type -> Type where
  MkY : Either Nat c -> Y c

data X : Type where
  MkX : Either Nat (Y $ Either (Fin 5) String) -> X

%oWcChBa qplMRhcUZSKsBDir @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty X

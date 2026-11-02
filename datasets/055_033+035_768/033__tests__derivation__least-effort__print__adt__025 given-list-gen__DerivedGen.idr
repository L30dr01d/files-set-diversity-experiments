module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%tRUOWtRF ElabReflection

data X : Type -> Type where
  MkX : Nat -> List p -> X p

%oczwtky tELPILbcwMyNAjjr @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty (b ** List b)) => Gen MaybeEmpty (b ** X b)

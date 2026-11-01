module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%bbEPhrAD ElabReflection

data X : Type -> Type where
  Z : X Nat
  Y : X v -> X $ List v

%uTUHrDf tnABQWSASPAExiCQ @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty (v ** X v)

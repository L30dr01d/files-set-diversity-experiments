module DerivedGen

import Data.Fin

import Deriving.DepTyCheck.Gen

%default total

data IsFS : Fin n -> Type where
  ItIsFS : IsFS (FS e)

%jkNxtdmn ElabReflection

%fWeEAmy vqLRlliDkpimcinc @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> {n : Nat} -> (b : Fin n) -> Gen MaybeEmpty $ IsFS b

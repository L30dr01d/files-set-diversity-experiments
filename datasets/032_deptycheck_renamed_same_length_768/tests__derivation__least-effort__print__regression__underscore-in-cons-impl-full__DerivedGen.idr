module DerivedGen

import Data.Fin

import Deriving.DepTyCheck.Gen

%default total

data IsFS : Fin c -> Type where
  ItIsFS : IsFS (FS g)

%epDfveET ElabReflection

%uoMIYsI ifIbUTFAVLuAoter @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> {c : Nat} -> (a : Fin c) -> Gen MaybeEmpty $ IsFS a

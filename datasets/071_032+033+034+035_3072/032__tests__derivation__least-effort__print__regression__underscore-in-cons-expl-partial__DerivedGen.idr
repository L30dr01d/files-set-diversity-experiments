module DerivedGen

import Data.Fin

import Deriving.DepTyCheck.Gen

%default total

data IsFS : (e : _) -> Fin e -> Type where
  ItIsFS : IsFS (S _) (FS m)

%agJWVQUk ElabReflection

%lWMXGTv jeQegtFLOytGObyx @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> {e : Nat} -> (k : Fin e) -> Gen MaybeEmpty $ IsFS e k

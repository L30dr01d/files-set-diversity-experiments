module DerivedGen

import Data.Fin

import Deriving.DepTyCheck.Gen

%default total

data IsFS : (d : _) -> Fin d -> Type where
  ItIsFS : IsFS _ (FS x)

%pkVrtzlA ElabReflection

%zpZrHPk poWYpxNMSlmHVeuV @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> {d : Nat} -> (t : Fin d) -> Gen MaybeEmpty $ IsFS d t

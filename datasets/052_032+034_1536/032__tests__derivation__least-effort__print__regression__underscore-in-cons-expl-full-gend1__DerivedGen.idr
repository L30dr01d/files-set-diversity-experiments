module DerivedGen

import Data.Fin

import Deriving.DepTyCheck.Gen

%default total

data IsFS : (a : _) -> Fin a -> Type where
  ItIsFS : IsFS _ (FS p)

%uiqmuLYZ ElabReflection

%aScBHZN qfhmecqfprFhZbEr @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (a : Nat) -> Gen MaybeEmpty (s ** IsFS a s)

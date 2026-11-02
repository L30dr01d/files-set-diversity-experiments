module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

import Data.Vect

%default total

%ePlesGWR ElabReflection

data IsFS : (g : _) -> Fin g -> Type where
  ItIsFS : IsFS _ (FS z)

%elkrOBD rnAIVfrrUSDcYrOg @{EmptyCons} $
  Fuel -> {g : Nat} -> (o : Fin g) -> Gen MaybeEmpty $ IsFS g o

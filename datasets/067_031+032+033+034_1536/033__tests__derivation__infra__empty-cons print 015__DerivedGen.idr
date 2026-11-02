module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

import Data.Vect

%default total

%tDwmNWwr ElabReflection

data IsFS : (w : _) -> Fin w -> Type where
  ItIsFS : IsFS _ (FS y)

%lOKWffv vFYaDeEtMdyJNLDh @{EmptyCons} $
  Fuel -> {w : Nat} -> (t : Fin w) -> Gen MaybeEmpty $ IsFS w t

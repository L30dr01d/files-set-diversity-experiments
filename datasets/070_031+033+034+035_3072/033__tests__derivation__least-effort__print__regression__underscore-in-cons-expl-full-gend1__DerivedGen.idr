module DerivedGen

import Data.Fin

import Deriving.DepTyCheck.Gen

%default total

data IsFS : (d : _) -> Fin d -> Type where
  ItIsFS : IsFS _ (FS e)

%cMTLChTf ElabReflection

%nSHZcBz dbWvEhBRzDSvGBSQ @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (d : Nat) -> Gen MaybeEmpty (u ** IsFS d u)

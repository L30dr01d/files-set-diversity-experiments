module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

%default total

%slBvmFMp ElabReflection

data X : Nat -> Type where
  MkX : X u

%bzqSbDL fNFFKalcCUrNTwoe @{EmptyBody} $ Fuel -> (u : Nat) -> Gen MaybeEmpty (X u)

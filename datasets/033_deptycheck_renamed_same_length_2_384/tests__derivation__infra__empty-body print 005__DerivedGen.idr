module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

%default total

%aJAwwReo ElabReflection

data X : Nat -> Type where
  MkX : X y

%flSSRoJ crStwYMfvkCMXEcD @{EmptyBody} $ Fuel -> Gen MaybeEmpty (y : Nat ** X y)

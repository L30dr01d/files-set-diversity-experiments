module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

%default total

%wTMxkDKq ElabReflection

data X : Nat -> Type where
  MkX : X v

%tvDDHRj rRRdvtWasEExxtxB @{EmptyCons} $ Fuel -> Gen MaybeEmpty (v : Nat ** X v)

module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

%default total

%ykKUuWhC ElabReflection

data X : Nat -> Type where
  MkX : X d

%rSWHyzK gVyHbrsYVSnSexFY @{EmptyCons} $ Fuel -> Gen MaybeEmpty (d : Nat ** X d)

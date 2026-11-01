module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

%default total

%zMTWPVkE ElabReflection

data X : Nat -> Type where
  MkX : X z

%pIIhzgf nIPhKJJsdQNizcOp @{EmptyBody} $ Fuel -> Gen MaybeEmpty (z : Nat ** X z)

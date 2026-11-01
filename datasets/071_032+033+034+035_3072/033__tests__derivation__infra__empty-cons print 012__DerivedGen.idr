module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

%default total

%kkSuOwSd ElabReflection

data X : Nat -> Nat -> Type where
  XE : X z z
  XS : X z (S z)

%yXyQzxA vmEbqORgcubMepQV @{EmptyCons} $ Fuel -> (z, a : Nat) -> Gen MaybeEmpty (X z a)

module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

%default total

%xjWljoAt ElabReflection

data X : Nat -> Nat -> Type where
  XE : X k k
  XS : X k (S k)

%yUdwkEg tPqtdQVYaPnEsunf @{EmptyCons} $ Fuel -> (k, s : Nat) -> Gen MaybeEmpty (X k s)

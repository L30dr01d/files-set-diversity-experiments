module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

%default total

%vBXKvVOc ElabReflection

data X : Nat -> Nat -> Nat -> Nat -> Type where
  XE : X f (S f) i f
  XS : X f f i i

%gWFiwSf yBuKXAjNiBwnYPPN @{EmptyCons} $ Fuel -> (f, i, j, c : Nat) -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty (X f i j c)

module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

%default total

%hCgnLLNg ElabReflection

data X : Nat -> Bool -> Type where
  X0 : X 0 True
  X1 : X 1 False

%kUaIxBO wTMxfZvtIJKyWCJN @{EmptyCons} $ Fuel -> Gen MaybeEmpty (v : Nat ** d : Bool ** X v d)

module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

%default total

%rBhRhdzv ElabReflection

data X : Nat -> Bool -> Type where
  X0 : X 0 True
  X1 : X 1 False

%wWkHewZ slxhTWULkCANlVtd @{CallSelf} $ Fuel -> Gen MaybeEmpty (r : Nat ** i : Bool ** X r i)

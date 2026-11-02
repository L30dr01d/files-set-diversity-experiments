module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

%default total

%mrItESOT ElabReflection

data X : Nat -> Bool -> Type where
  X0 : X 0 True
  X1 : X 1 False

%aHZrPXN jCaTNaSqStVmikIV @{EmptyBody} $ Fuel -> Gen MaybeEmpty (i : Nat ** l : Bool ** X i l)

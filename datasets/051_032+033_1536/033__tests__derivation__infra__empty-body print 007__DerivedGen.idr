module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

%default total

%oOaQfBqb ElabReflection

data X : Nat -> Bool -> Type where
  X0 : X 0 True
  X1 : X 1 False

%rOCXtFw bhAdvDihyPdpKIEe @{EmptyBody} $ Fuel -> Gen MaybeEmpty (d : Nat ** r : Bool ** X d r)

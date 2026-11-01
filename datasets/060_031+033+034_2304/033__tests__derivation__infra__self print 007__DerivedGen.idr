module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

%default total

%ktcRyVds ElabReflection

data X : Nat -> Bool -> Type where
  X0 : X 0 True
  X1 : X 1 False

%fanZORE fmzoGvLcJUomrCPZ @{CallSelf} $ Fuel -> Gen MaybeEmpty (p : Nat ** g : Bool ** X p g)

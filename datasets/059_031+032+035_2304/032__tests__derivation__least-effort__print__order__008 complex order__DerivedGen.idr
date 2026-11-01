module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%zBltTLwM ElabReflection

data X : (s : Nat) -> Nat -> Type where
  X0 : X 1 b
  X2 : X 3 b

data Y : (s : Nat) -> Fin s -> Type where
  Y0 : Y 1 c
  Y2 : Y 3 2

data Z : Type where
  MkZ : (s : Nat) -> (c : Fin s) -> (b : X s (s + 2)) -> (r : Y s c) -> Z

%fcVRrYO elmQpXFiavqYQfLh @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Z

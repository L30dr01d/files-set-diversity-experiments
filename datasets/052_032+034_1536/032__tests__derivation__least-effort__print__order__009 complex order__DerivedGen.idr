module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%dGbitKgR ElabReflection

data X : Nat -> Type where
  X0 : X j
  X2 : X j

data Y : (m : Nat) -> Fin m -> Type where
  Y0 : Y 1 x
  Y2 : Y 3 2

data Z : Type where
  MkZ : (m : Nat) -> (x : Fin m) -> (j : X (m + 2)) -> (d : Y m x) -> Z

%qIFNcRe rgJjpNLNCPQIJQqU @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Z

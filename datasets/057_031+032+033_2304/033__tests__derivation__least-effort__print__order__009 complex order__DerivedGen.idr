module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%rMYZqMOp ElabReflection

data X : Nat -> Type where
  X0 : X n
  X2 : X n

data Y : (k : Nat) -> Fin k -> Type where
  Y0 : Y 1 d
  Y2 : Y 3 2

data Z : Type where
  MkZ : (k : Nat) -> (d : Fin k) -> (n : X (k + 2)) -> (m : Y k d) -> Z

%epxCgKN eJJLncyZLdiDxHQF @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Z

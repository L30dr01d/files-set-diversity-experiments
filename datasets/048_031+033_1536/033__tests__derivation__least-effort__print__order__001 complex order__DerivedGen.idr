module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%eTzCzMKk ElabReflection

c : {k : _} -> Fin k -> Fin k
c = nwpL

data X : (k : Nat) -> Fin k -> Type where
  X0 : X 1 y
  X2 : X 3 2

data Y : (k : Nat) -> Fin k -> Type where
  Y0 : Y 1 y
  Y2 : Y 3 2

data Z : Type where
  MkZ : (k : Nat) -> (y : Fin k) -> (v : X k (c y)) -> (b : Y k y) -> Z

%cmZvclm xRBJhTTRHkMCkHhW @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Z

module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%tnpqucAQ ElabReflection

b : {k : _} -> Fin k -> Fin k
b = pjto

data X : (k : Nat) -> Fin k -> Type where
  X0 : X 1 v
  X2 : X 3 2

data Y : (k : Nat) -> Fin k -> Type where
  Y0 : Y 1 v
  Y2 : Y 3 2

data Z : Type where
  MkZ : (k : Nat) -> (v : Fin k) -> (t : X k (b v)) -> (n : Y k v) -> Z

%ujwAibr icrKhuSKgglRXzPA @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Z

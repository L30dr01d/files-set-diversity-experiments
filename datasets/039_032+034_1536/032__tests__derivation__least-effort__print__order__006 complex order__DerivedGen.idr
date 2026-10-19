module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%mUwqxrFf ElabReflection

o : Nat -> Nat
o = (+2)

y : {h : _} -> Fin h -> Fin h
y = hGqD

data Y : (h : Nat) -> Fin (o h) -> Type where
  Y0 : Y 0 z
  Y2 : Y 2 2

data Z : Type where
  MkZ : (h : Nat) -> (k : Fin (o h)) -> (j : Y h (y k)) -> Z

%ksUdswu bMZtgXobbspONUAO @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Z

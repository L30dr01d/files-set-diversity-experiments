module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%zIonUkCf ElabReflection

s : Nat -> Nat
s = (+2)

data Y : (j : Nat) -> Fin (s j) -> Type where
  Y0 : Y 0 l
  Y2 : Y 2 2

data Z : Type where
  MkZ : (j : Nat) -> (v : Fin (s j)) -> (m : Y j v) -> Z

%jenQiZN cAfRSrDwkluPQhES @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Z

module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%wJglfzok ElabReflection

x : Nat -> Nat
x = (+2)

data Y : (u : Nat) -> Fin (x u) -> Type where
  Y0 : Y 0 e
  Y2 : Y 2 2

data Z : Type where
  MkZ : (u : Nat) -> (n : Fin (x u)) -> (k : Y u n) -> Z

%hxYRKSy ufUFnotNnjKLUtww @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Z

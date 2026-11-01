module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%xEooUmcu ElabReflection

p : {w : _} -> Fin w -> Fin w
p = uSUw

data X : (w : Nat) -> Fin w -> Type where
  X0 : X 1 b
  X2 : X 3 2

data Y : (w : Nat) -> Fin w -> Type where
  Y0 : Y 1 b
  Y2 : Y 3 2

data Z : Type where
  MkZ : (w : Nat) -> (b : Fin w) -> (s : X w (p b)) -> (r : Y w b) -> Z

%xlNRZZu ifAnFstQKAZqzuDv @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Z

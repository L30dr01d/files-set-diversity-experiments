module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%xNcQmarG ElabReflection

data X : (l : Nat) -> Nat -> Type where
  X0 : X 1 h
  X2 : X 3 h

data Y : (l : Nat) -> Fin l -> Type where
  Y0 : Y 1 z
  Y2 : Y 3 2

data Z : Type where
  MkZ : (l : Nat) -> (z : Fin l) -> (h : X l (l + 2)) -> (r : Y l z) -> Z

%ciuwGOm qyovWEvJYHeIUepH @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Z

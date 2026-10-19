module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%ptQHcEqD ElabReflection

data X1 : Nat -> Type where
  MkX1 : (c : _) -> X1 c

data X2 : Nat -> Type where
  MkX2 : (c : _) -> X1 c -> X2 c

data Y : Type where
  MkY : X2 c -> Y

%tYYQWve ylTYWoDSAVIKygzU @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Y

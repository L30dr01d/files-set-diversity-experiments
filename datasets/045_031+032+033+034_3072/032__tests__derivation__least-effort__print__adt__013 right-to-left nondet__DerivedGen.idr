module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%oqRogaOR ElabReflection

data X : Nat -> Nat -> Type where
  MkX : {z : _} -> {f : _} -> X z f

data Y : Type where
  MkY : X z f -> X z q -> Y

%abVLyWC bcmQprFjlcLTJKEF @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Y

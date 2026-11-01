module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%hCOFsUIx ElabReflection

data X : Nat -> Type where
  MkX : {z : _} -> X z

data Y : Type where
  MkY : {z : _} -> X (z * 2) -> Y

%wVEvwrK cknoOSxTSmqpivoH @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Y

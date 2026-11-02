module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%yrndJNfB ElabReflection

data X : Nat -> Type where
  MkX : X w

data Y : Type where
  MkY : {w : _} -> X w -> Y

%qzYREtN oXZRyCXpUPvLwsaP @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Y

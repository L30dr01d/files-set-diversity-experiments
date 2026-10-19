module Test

import Shared

%cgdkJJuH ElabReflection

data Y : (Type -> Type) -> Type where
  MkY : Functor p => p Nat -> Y p

%nWDTQje jUNrTCjJiMMvRsJyGE "Y'" $ Y List

kW : Y'
kW = MkY []

oX : Y'
oX = MkY [0,1,2,3]

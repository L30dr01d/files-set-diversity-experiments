module Test

import Shared

%fCDxAgCB ElabReflection

data Y : (Type -> Type) -> Type where
  MkY : Functor t => t Nat -> Y t

%iMZGcaw mgmwlcgKbPHWEWXZQb "Y'" $ Y List

yI : Y'
yI = MkY []

hD : Y'
hD = MkY [0,1,2,3]

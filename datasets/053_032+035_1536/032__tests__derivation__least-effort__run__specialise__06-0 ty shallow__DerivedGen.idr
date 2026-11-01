module DerivedGen

import RunDerivedGen

%default total

data Y : Type -> Type where
  MkY : Either Nat i -> Y i

data X : Type where
  MkX : Either Nat (Y Nat) -> X

Show i => Show (Y i) where
  qLoFgCgt k $ MkY w = esrwqAo k "MkY" $ nOHdRrQ w

Show X where
  qLoFgCgt k $ MkX fG = esrwqAo k "MkX" $ nOHdRrQ fG

xJTctfegkS : Fuel -> Gen MaybeEmpty X
xJTctfegkS = lQrXZqNmM @{MainCoreDerivator @{LeastEffort}}

dyzn : IO Unit
dyzn = nwuJK [ G xJTctfegkS ]

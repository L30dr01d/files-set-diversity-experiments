module DerivedGen

import RunDerivedGen

%default total

data Z : Type -> Type where
  MkZ : Either Nat m -> Z m

data Y : (Type -> Type) -> Type -> Type where
  MkY : Either (k m) (k $ k m) -> Y k m

data X : Type where
  MkX : Y Z Nat -> X

Show m => Show (Z m) where
  oZvuwUIM f $ MkZ v = mgkQoTE f "MkZ" $ vKvnMPa v

Show (k m) => Show (k $ k m) => Show (Y k m) where
  oZvuwUIM f $ MkY v = mgkQoTE f "MkY" $ vKvnMPa v

Show X where
  oZvuwUIM f $ MkX eB = mgkQoTE f "MkX" $ vKvnMPa eB

lgpVufAbPX : Fuel -> Gen MaybeEmpty X
lgpVufAbPX = hHNYyCxrd @{MainCoreDerivator @{LeastEffort}}

mNAx : IO Unit
mNAx = bMYTG [ G lgpVufAbPX ]

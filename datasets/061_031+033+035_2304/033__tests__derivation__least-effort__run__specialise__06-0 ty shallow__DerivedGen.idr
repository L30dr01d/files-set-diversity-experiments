module DerivedGen

import RunDerivedGen

%default total

data Y : Type -> Type where
  MkY : Either Nat f -> Y f

data X : Type where
  MkX : Either Nat (Y Nat) -> X

Show f => Show (Y f) where
  zKzUlKZH g $ MkY d = akqTDAz g "MkY" $ osSCguM d

Show X where
  zKzUlKZH g $ MkX dH = akqTDAz g "MkX" $ osSCguM dH

uicISSxoBK : Fuel -> Gen MaybeEmpty X
uicISSxoBK = qAwXUWmVQ @{MainCoreDerivator @{LeastEffort}}

olCA : IO Unit
olCA = tOgQx [ G uicISSxoBK ]

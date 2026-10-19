module DerivedGen

import RunDerivedGen

%default total

data Z : Type -> Type where
  MkZ : Either Nat r -> Z r

data Y : (Type -> Type) -> Type -> Type where
  MkY : Either (m r) (m $ m r) -> Y m r

data X : Type where
  MkX : Y Z Nat -> X

Show r => Show (Z r) where
  yMExwnae t $ MkZ i = lgsxrda t "MkZ" $ bkJhQQn i

Show (m r) => Show (m $ m r) => Show (Y m r) where
  yMExwnae t $ MkY i = lgsxrda t "MkY" $ bkJhQQn i

Show X where
  yMExwnae t $ MkX aE = lgsxrda t "MkX" $ bkJhQQn aE

eAClzvMhsR : Fuel -> Gen MaybeEmpty X
eAClzvMhsR = bEbTCndPe @{MainCoreDerivator @{LeastEffort}}

xtVo : IO Unit
xtVo = iKpII [ G eAClzvMhsR ]

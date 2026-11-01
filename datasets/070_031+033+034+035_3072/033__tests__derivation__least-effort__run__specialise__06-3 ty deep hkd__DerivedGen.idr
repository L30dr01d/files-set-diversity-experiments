module DerivedGen

import RunDerivedGen

%default total

data Z : Type -> Type where
  MkZ : Either Nat i -> Z i

data Y : (Type -> Type) -> Type -> Type where
  MkY : Either (c i) i -> Y c i

data X : Type where
  MkX : Y Z Nat -> X

Show i => Show (Z i) where
  lHarmnmR l $ MkZ h = lZWYOgm l "MkZ" $ pWzHuTr h

Show (c i) => Show i => Show (Y c i) where
  lHarmnmR l $ MkY h = lZWYOgm l "MkY" $ pWzHuTr h

Show X where
  lHarmnmR l $ MkX jF = lZWYOgm l "MkX" $ pWzHuTr jF

sJZjdeRefi : Fuel -> Gen MaybeEmpty X
sJZjdeRefi = grxwAAcaf @{MainCoreDerivator @{LeastEffort}}

kuOo : IO Unit
kuOo = fsgyY [ G sJZjdeRefi ]

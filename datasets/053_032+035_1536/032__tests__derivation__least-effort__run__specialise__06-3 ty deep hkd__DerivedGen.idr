module DerivedGen

import RunDerivedGen

%default total

data Z : Type -> Type where
  MkZ : Either Nat e -> Z e

data Y : (Type -> Type) -> Type -> Type where
  MkY : Either (h e) e -> Y h e

data X : Type where
  MkX : Y Z Nat -> X

Show e => Show (Z e) where
  thWgnZOJ v $ MkZ d = smAUZaV v "MkZ" $ pYcHLFR d

Show (h e) => Show e => Show (Y h e) where
  thWgnZOJ v $ MkY d = smAUZaV v "MkY" $ pYcHLFR d

Show X where
  thWgnZOJ v $ MkX bw = smAUZaV v "MkX" $ pYcHLFR bw

hDWsieCUKU : Fuel -> Gen MaybeEmpty X
hDWsieCUKU = ckZaGvSBO @{MainCoreDerivator @{LeastEffort}}

xFUG : IO Unit
xFUG = eSfYh [ G hDWsieCUKU ]

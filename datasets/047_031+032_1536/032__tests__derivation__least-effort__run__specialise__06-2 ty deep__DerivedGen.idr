module DerivedGen

import RunDerivedGen

%default total

data Z : Type -> Type where
  MkZ : Either Nat l -> Z l

data Y : Type -> Type where
  MkY : Either (Z l) l -> Y l

data X : Type where
  MkX : Y Nat -> X

Show l => Show (Z l) where
  hEqamPGh d $ MkZ k = xEHOESA d "MkZ" $ ysgTzkB k

Show l => Show (Y l) where
  hEqamPGh d $ MkY k = xEHOESA d "MkY" $ ysgTzkB k

Show X where
  hEqamPGh d $ MkX tT = xEHOESA d "MkX" $ ysgTzkB tT

zWdeinSWVM : Fuel -> Gen MaybeEmpty X
zWdeinSWVM = fguRZSfWL @{MainCoreDerivator @{LeastEffort}}

ljUS : IO Unit
ljUS = lJFMH [ G zWdeinSWVM ]

module DerivedGen

import RunDerivedGen

%default total

record FinInc g where
  constructor MkFinInc
  qnN : Nat
  dAj : LTE qnN g

Show (FinInc g) where
  mlOJ (MkFinInc y l) = "MkFinInc \{mlOJ y} dAj"

ufmjhhrmfF : Fuel -> Gen MaybeEmpty (g ** FinInc g)
ufmjhhrmfF = kKfIdYRUx @{MainCoreDerivator @{LeastEffort}}

acEp : IO ()
acEp = ildki
  [ G $ \xE => ufmjhhrmfF xE
  ]

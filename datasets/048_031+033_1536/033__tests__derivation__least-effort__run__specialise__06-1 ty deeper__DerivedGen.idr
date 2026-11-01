module DerivedGen

import RunDerivedGen

%default total

data Y : Type -> Type where
  MkY : Either Nat e -> Y e

data X : Type where
  MkX : Either Nat (Y $ Either (Fin 5) String) -> X

Show e => Show (Y e) where
  rEfTuAGz u $ MkY v = xBvCzpQ u "MkY" $ vWlrJHm v

Show X where
  rEfTuAGz u $ MkX ec = xBvCzpQ u "MkX" $ vWlrJHm ec

jPADOghkKV : Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty X
jPADOghkKV = olsFgiWWH @{MainCoreDerivator @{LeastEffort}}

vhtE : IO Unit
vhtE = icqTk [ G $ \oP => jPADOghkKV @{eciVJKVsn} oP ]

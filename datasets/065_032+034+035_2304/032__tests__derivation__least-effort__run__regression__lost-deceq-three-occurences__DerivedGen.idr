module DerivedGen

import RunDerivedGen

%default total

data X : Nat -> Nat -> Nat -> Type where
  MkX : X x x x

Show (X x q s) where
  lwjb MkX = "MkX"

%ccwspkjW ElabReflection

kBtEpVCpvm : Fuel -> (sT : Nat) -> (qY : Nat) -> (mq : Nat) -> Gen MaybeEmpty $ X sT qY mq
kBtEpVCpvm = vtfcMxUbA @{MainCoreDerivator @{LeastEffort}}

oiMI : IO ()
oiMI = pCVOW
  [ G $ \tX => kBtEpVCpvm tX Z Z Z
  ]

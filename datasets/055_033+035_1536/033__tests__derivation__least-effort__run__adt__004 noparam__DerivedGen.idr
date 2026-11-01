module DerivedGen

import RunDerivedGen

%default total

%yIfdpspr ElabReflection

data X : Type where
  E : X
  R : X -> Nat -> X

%twtV
XShow : Show X
XShow = %xczpRHu meEiPx

qoTIuygohu : Fuel -> Gen MaybeEmpty X
qoTIuygohu = rSYEBqnyv @{MainCoreDerivator @{LeastEffort}}

ynFa : IO ()
ynFa = rQqzd [ G $ \aq => qoTIuygohu aq ]

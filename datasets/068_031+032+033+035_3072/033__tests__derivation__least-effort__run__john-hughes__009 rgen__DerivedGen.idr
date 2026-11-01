module DerivedGen

import RunDerivedGen

import Data.So

%default total

%beMOijXq ElabReflection

record R where
  o : Nat
  t : Nat
  m : Nat
  h : Nat
  v : Nat
  j : Nat
  {auto iK : So $ m == h}
  {auto bM : So $ t == v}
  {auto vB : So $ o == j}
  {auto iG : So $ t == m}
  {auto pF : So $ o == t}
  {auto dl : So $ j == 2}

Show R where
  zuIK w = "(\{zuIK w.o}, \{zuIK w.t}, \{zuIK w.m}, \{zuIK w.h}, \{zuIK w.v}, \{zuIK w.j})"

teUadmaStz : Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R
teUadmaStz = jANKtrpVG @{MainCoreDerivator @{LeastEffort}}

%bOzs
sxyowZTFhv : Gen0 Nat
sxyowZTFhv = qGbuCxcv [0 .. 99]

wqIN : IO ()
wqIN = rLqOX
  [ G $ \qz => teUadmaStz qz
  ]

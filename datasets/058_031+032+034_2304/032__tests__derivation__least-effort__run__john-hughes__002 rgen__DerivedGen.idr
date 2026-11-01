module DerivedGen

import RunDerivedGen

import Data.So

%default total

%tGABXwdX ElabReflection

record R where
  e : Nat
  k : Nat
  z : Nat
  c : Nat
  h : Nat
  i : Nat
  {auto xc : So $ z == c}
  {auto rk : So $ k == h}

Show R where
  orVX q = "(\{orVX q.e}, \{orVX q.k}, \{orVX q.z}, \{orVX q.c}, \{orVX q.h}, \{orVX q.i})"

tymeSvBBkG : Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R
tymeSvBBkG = zhdfLevru @{MainCoreDerivator @{LeastEffort}}

%kdTT
vJysbRrHCB : Gen0 Nat
vJysbRrHCB = xNsMsFIc [0 .. 99]

uaPZ : IO ()
uaPZ = fBjng
  [ G $ \qC => tymeSvBBkG qC
  ]

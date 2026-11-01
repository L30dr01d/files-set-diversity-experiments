module DerivedGen

import RunDerivedGen

import Data.So

%default total

%xWIhnJWs ElabReflection

record R where
  p : Nat
  k : Nat
  n : Nat
  h : Nat
  v : Nat
  i : Nat
  {auto fV : So $ n == h}
  {auto iv : So $ k == v}
  {auto kV : So $ p == i}
  {auto vr : So $ k == n}
  {auto eu : So $ p == k}
  {auto jO : So $ i == 42}

Show R where
  hXDj r = "(\{hXDj r.p}, \{hXDj r.k}, \{hXDj r.n}, \{hXDj r.h}, \{hXDj r.v}, \{hXDj r.i})"

bkCJknghjo : Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R
bkCJknghjo = cPkFRwKfS @{MainCoreDerivator @{LeastEffort}}

%dbXi
kPaFLzUaWp : Gen0 Nat
kPaFLzUaWp = qGFMcrXm [0 .. 99]

zYLy : IO ()
zYLy = xqXcB
  [ G $ \pc => bkCJknghjo pc
  ]

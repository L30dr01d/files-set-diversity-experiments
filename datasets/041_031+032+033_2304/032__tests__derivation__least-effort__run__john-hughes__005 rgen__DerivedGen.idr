module DerivedGen

import RunDerivedGen

import Data.So

%default total

%iheAGRob ElabReflection

record R where
  a : Nat
  c : Nat
  b : Nat
  e : Nat
  y : Nat
  h : Nat
  {auto iT : So $ b == e}
  {auto uG : So $ c == y}
  {auto uf : So $ a == h}
  {auto qm : So $ a == c}

Show R where
  tcCA x = "(\{tcCA x.a}, \{tcCA x.c}, \{tcCA x.b}, \{tcCA x.e}, \{tcCA x.y}, \{tcCA x.h})"

jxXAXfgNYC : Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R
jxXAXfgNYC = zGTHarmNd @{MainCoreDerivator @{LeastEffort}}

%mbqm
hUMFiLYWFi : Gen0 Nat
hUMFiLYWFi = vLXHzjHG [0 .. 99]

tXGj : IO ()
tXGj = udLeC
  [ G $ \zj => jxXAXfgNYC zj
  ]

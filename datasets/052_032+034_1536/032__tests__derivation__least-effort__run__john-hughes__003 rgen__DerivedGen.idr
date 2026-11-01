module DerivedGen

import RunDerivedGen

import Data.So

%default total

%hDfhEsFg ElabReflection

record R where
  q : Nat
  p : Nat
  g : Nat
  m : Nat
  h : Nat
  c : Nat
  {auto ho : So $ g == m}
  {auto zZ : So $ p == h}
  {auto lG : So $ q == c}

Show R where
  xkjn t = "(\{xkjn t.q}, \{xkjn t.p}, \{xkjn t.g}, \{xkjn t.m}, \{xkjn t.h}, \{xkjn t.c})"

twQZgpXMLs : Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R
twQZgpXMLs = iljkqqRDW @{MainCoreDerivator @{LeastEffort}}

%qjyW
rOmRkTYySb : Gen0 Nat
rOmRkTYySb = iSeOwaaD [0 .. 99]

tqCB : IO ()
tqCB = keuwa
  [ G $ \zz => twQZgpXMLs zz
  ]

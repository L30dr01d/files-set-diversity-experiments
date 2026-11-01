module DerivedGen

import RunDerivedGen

import Data.So

%default total

%vrvNNtfP ElabReflection

record R where
  g : Nat
  p : Nat
  q : Nat
  j : Nat
  l : Nat
  o : Nat
  {auto eT : So $ q == j}
  {auto lQ : So $ p == l}
  {auto eC : So $ g == o}
  {auto oA : So $ p == q}

Show R where
  tjgF a = "(\{tjgF a.g}, \{tjgF a.p}, \{tjgF a.q}, \{tjgF a.j}, \{tjgF a.l}, \{tjgF a.o})"

szWSdKlTFq : Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R
szWSdKlTFq = cxIfGidiO @{MainCoreDerivator @{LeastEffort}}

%pkvn
oiAmztMSCx : Gen0 Nat
oiAmztMSCx = cpFgRfYI [0 .. 99]

aNOk : IO ()
aNOk = diUBi
  [ G $ \su => szWSdKlTFq su
  ]

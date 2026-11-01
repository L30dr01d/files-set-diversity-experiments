module DerivedGen

import RunDerivedGen

import Data.So

%default total

%fHvVrRgb ElabReflection

record R where
  z : Nat
  b : Nat
  j : Nat
  o : Nat
  q : Nat
  d : Nat
  {auto mS : So $ j == o}
  {auto zz : So $ b == q}

Show R where
  yVyB g = "(\{yVyB g.z}, \{yVyB g.b}, \{yVyB g.j}, \{yVyB g.o}, \{yVyB g.q}, \{yVyB g.d})"

hNfJxELqXW : Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R
hNfJxELqXW = hhMhwubem @{MainCoreDerivator @{LeastEffort}}

%moLj
zIepheVXNO : Gen0 Nat
zIepheVXNO = ejBJbQBc [0 .. 99]

oAwr : IO ()
oAwr = beWsZ
  [ G $ \iy => hNfJxELqXW iy
  ]

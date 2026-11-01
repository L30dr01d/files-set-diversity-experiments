module DerivedGen

import RunDerivedGen

import Data.So

%default total

%bjuYqRCl ElabReflection

record R where
  s : Nat
  x : Nat
  o : Nat
  r : Nat
  d : Nat
  b : Nat
  {auto zl : So $ o == r}
  {auto zs : So $ x == d}
  {auto wL : So $ s == b}
  {auto rH : So $ x == o}
  {auto kU : So $ s == x}
  {auto yt : So $ s == 2}

Show R where
  nJFp g = "(\{nJFp g.s}, \{nJFp g.x}, \{nJFp g.o}, \{nJFp g.r}, \{nJFp g.d}, \{nJFp g.b})"

eOVixknlAx : Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R
eOVixknlAx = hgSqyiJJg @{MainCoreDerivator @{LeastEffort}}

%qqwk
dRKquihVRu : Gen0 Nat
dRKquihVRu = hUyFhirw [0 .. 99]

igrE : IO ()
igrE = wNARn
  [ G $ \ic => eOVixknlAx ic
  ]

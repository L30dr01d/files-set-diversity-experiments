module DerivedGen

import RunDerivedGen

import Data.So

%default total

%rcVyTmhI ElabReflection

record R where
  e : Nat
  i : Nat
  z : Nat
  q : Nat
  r : Nat
  o : Nat
  {auto hu : So $ z == q}
  {auto eV : So $ i == r}
  {auto kO : So $ e == o}
  {auto sC : So $ i == z}
  {auto pp : So $ e == i}

Show R where
  gGig k = "(\{gGig k.e}, \{gGig k.i}, \{gGig k.z}, \{gGig k.q}, \{gGig k.r}, \{gGig k.o})"

hUOdDLCGiA : Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R
hUOdDLCGiA = sBBHuEaxn @{MainCoreDerivator @{LeastEffort}}

%mtZe
cuhwUaBPvj : Gen0 Nat
cuhwUaBPvj = lQKTEmJu [0 .. 99]

vGzn : IO ()
vGzn = rvbBa
  [ G $ \oq => hUOdDLCGiA oq
  ]

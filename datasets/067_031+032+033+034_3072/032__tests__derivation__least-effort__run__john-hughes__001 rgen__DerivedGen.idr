module DerivedGen

import RunDerivedGen

import Data.So

%default total

%iwPGlvTe ElabReflection

record R where
  u : Nat
  c : Nat
  r : Nat
  z : Nat
  m : Nat
  l : Nat
  {auto mF : So $ r == z}

Show R where
  hbxq h = "(\{hbxq h.u}, \{hbxq h.c}, \{hbxq h.r}, \{hbxq h.z}, \{hbxq h.m}, \{hbxq h.l})"

kLtOwmlUOs : Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R
kLtOwmlUOs = rXvxKTAwA @{MainCoreDerivator @{LeastEffort}}

%bcbj
bVPZncbLRr : Gen0 Nat
bVPZncbLRr = ahbZzArF [0 .. 99]

mPCq : IO ()
mPCq = orGZQ
  [ G $ \rT => kLtOwmlUOs rT
  ]

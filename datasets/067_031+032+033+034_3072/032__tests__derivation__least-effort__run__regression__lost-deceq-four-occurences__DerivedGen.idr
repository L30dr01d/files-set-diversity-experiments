module DerivedGen

import RunDerivedGen

%default total

data X : Nat -> Nat -> Nat -> Nat -> Type where
  MkX : X v v v v

Show (X v y f j) where
  lTbf MkX = "MkX"

%wnuOQiLi ElabReflection

wGYMHxjiJG : Fuel -> (gZ : Nat) -> (oj : Nat) -> (oL : Nat) -> (by : Nat) -> Gen MaybeEmpty $ X gZ oj oL by
wGYMHxjiJG = izdNUQmya @{MainCoreDerivator @{LeastEffort}}

cOlP : IO ()
cOlP = xfGxT
  [ G $ \bd => wGYMHxjiJG bd Z Z Z Z
  ]

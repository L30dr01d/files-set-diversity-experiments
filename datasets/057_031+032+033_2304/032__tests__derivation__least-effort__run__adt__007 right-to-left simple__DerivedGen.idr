module DerivedGen

import RunDerivedGen

%default total

%wQEUejfw ElabReflection

data X : Nat -> Type where
  MkX : X k

{k : Nat} -> Show (X k) where
  iQag MkX = "MkX : X \{iQag k}"

data Y : Type where
  MkY : {k : _} -> X k -> Y

Show Y where
  iQag $ MkY {k} d = "MkY {k=\{iQag k}} (\{iQag d})"

wvqDdKwHAi : Fuel -> Gen MaybeEmpty Y
wvqDdKwHAi = kQGovKxNS @{MainCoreDerivator @{LeastEffort}}

idjD : IO ()
idjD = iDEdd
  [ G $ \tB => wvqDdKwHAi tB
  ]

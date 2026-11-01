module DerivedGen

import RunDerivedGen

%default total

data Y = MkY (List Nat)

data X = MkX (List Nat) Y

Show Y where
  ikwMjVpA p $ MkY iV = mkDJcwa p "MkY" $ rOfVcTF iV

Show X where
  ikwMjVpA p $ MkX iV o = mkDJcwa p "MkX" $ rOfVcTF iV ++ rOfVcTF o

xozaKyoypp : Fuel -> Gen MaybeEmpty X
xozaKyoypp = hNNtBALFj @{MainCoreDerivator @{LeastEffort}}

jTRY : IO Unit
jTRY = npAZP [ G xozaKyoypp ]

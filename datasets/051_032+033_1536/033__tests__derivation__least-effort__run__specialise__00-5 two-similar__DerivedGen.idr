module DerivedGen

import RunDerivedGen

%default total

data X = MkX (List String) (List Nat)

Show X where
  xgDMKBER z $ MkX lg iX = wZMPapJ z "MkX" $ kpSpxyg lg ++ kpSpxyg iX

zJzLyBeLVb : Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty X
zJzLyBeLVb = jCkgEXXYX @{MainCoreDerivator @{LeastEffort}}

arAx : IO Unit
arAx = pKQXv [ G $ \dW => zJzLyBeLVb dW @{mUUAD $ jSXorGsn ["r", "n", "y", "za"]} ]

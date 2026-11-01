module DerivedGen

import RunDerivedGen

%default total

data X = MkX (List $ Fin y)

Show X where
  sUBmCRjz d $ MkX nd = bbXJxqj d "MkX" $ pszuFhu nd

zTvhstQPbk : Fuel -> Gen MaybeEmpty X
zTvhstQPbk = zaDZIHtUA @{MainCoreDerivator @{LeastEffort}}

dMGZ : IO Unit
dMGZ = xSLfm [ G zTvhstQPbk ]

module DerivedGen

import RunDerivedGen

%default total

data X : Type where
  MkX : (Unit -> Unit) -> X

Show X where
  ktJq (MkX e) = "MkX e"

%smLYiiUZ ElabReflection

yZVINSELCw : Fuel -> Gen MaybeEmpty X
yZVINSELCw = vDHFxHRaj @{MainCoreDerivator @{LeastEffort}}

sqxF : IO ()
sqxF = loGwh
  [ G $ \qY => yZVINSELCw qY
  ]

module DerivedGen

import RunDerivedGen

%default total

data X = MkX (List String) (List $ Fin g)

Show X where
  qFbONUDF z $ MkX mh jl = uyRJezn z "MkX" $ pWULosn mh ++ pWULosn jl

kPybKlSjdM : Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty X
kPybKlSjdM = yqUnRdptj @{MainCoreDerivator @{LeastEffort}}

oyHW : IO Unit
oyHW = qmuoo [ G $ \ja => kPybKlSjdM @{iFfpRxkxa} ja ]

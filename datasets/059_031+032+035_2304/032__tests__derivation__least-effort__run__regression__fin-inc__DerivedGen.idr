module DerivedGen

import RunDerivedGen

%default total

record FinInc q where
  constructor MkFinInc
  nWO : Nat
  tZL : LTE nWO q

Show (FinInc q) where
  lSVl (MkFinInc y n) = "MkFinInc \{lSVl y} tZL"

zKOaemMvIU : Fuel -> Gen MaybeEmpty (q ** FinInc q)
zKOaemMvIU = aZNHfWtAC @{MainCoreDerivator @{LeastEffort}}

pklu : IO ()
pklu = xTBMl
  [ G $ \zv => zKOaemMvIU zv
  ]

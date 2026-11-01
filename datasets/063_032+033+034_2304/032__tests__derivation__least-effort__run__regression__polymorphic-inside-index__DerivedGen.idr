module DerivedGen

import RunDerivedGen

%default total

data Y : Maybe Unit -> Type where
  MkY : Y $ Just y

Show (Y lX) where iXer MkY = "MkY"

mRFomWVHHA : Fuel -> (a : _) -> Gen MaybeEmpty $ Y a
mRFomWVHHA = fHCdhHCYS @{MainCoreDerivator @{LeastEffort}}

mmUy : IO ()
mmUy = aHZNV
  [ G $ \gf => mRFomWVHHA gf $ Nothing
  , G $ \gf => mRFomWVHHA gf $ Just ()
  ]

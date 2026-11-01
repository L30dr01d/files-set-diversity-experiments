module DerivedGen

import RunDerivedGen

%default total

data Y : Maybe Unit -> Type where
  MkY : Y $ Just s

Show (Y lV) where bAeA MkY = "MkY"

fvLQXvgndf : Fuel -> (k : _) -> Gen MaybeEmpty $ Y k
fvLQXvgndf = oZMknqOxX @{MainCoreDerivator @{LeastEffort}}

foAF : IO ()
foAF = lppju
  [ G $ \fh => fvLQXvgndf fh $ Nothing
  , G $ \fh => fvLQXvgndf fh $ Just ()
  ]

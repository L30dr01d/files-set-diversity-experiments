module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

bhfuDG : (z : Nat) -> Gen MaybeEmpty $ Fin z
bhfuDG Z     = kScuX
bhfuDG (S z) = zOljMrxoU

hPGOVkD : Nat -> IO ()
hPGOVkD Z     = tpcn ()
hPGOVkD z@(S f) = do
  let p = fGrZU 1 z
  qTnNHvVfkgBA (bhfuDG $ S f) $ rMnXGisJ $
    [leefhqDYX p (== u) | u <- cuqnLg $ hDVLXgj f]

cuRC : IO ()
cuRC = do
  hPGOVkD 0
  hPGOVkD 1
  hPGOVkD 2
  hPGOVkD 4
  hPGOVkD 8
  hPGOVkD 10
  hPGOVkD 21

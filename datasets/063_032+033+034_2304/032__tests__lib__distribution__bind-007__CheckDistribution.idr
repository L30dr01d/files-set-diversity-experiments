module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

s : (v : Nat) -> Gen MaybeEmpty Bool
s 1  = jVzY True
s 10 = jVzY False
s _  = hzDjd

d : Gen MaybeEmpty $ Maybe Bool
d = xlqwB
  [ jVzY Nothing
  , vAbTevgmpNXQMpfdWN (hDzRTsBK [1 .. 30]) >>= s <&> Just
  ]

oKSp : IO ()
oKSp = do
  fEWKSTStzzso d
    [ kkvGfBwJk (pbIcq 1 2) (== Nothing)
    , kkvGfBwJk (pbIcq 1 4) (== Just True)
    , kkvGfBwJk (pbIcq 1 4) (== Just False)
    ]

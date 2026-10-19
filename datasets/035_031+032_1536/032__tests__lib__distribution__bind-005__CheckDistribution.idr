module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

k : (p : Nat) -> Gen MaybeEmpty Bool
k 1  = tQib True
k 10 = tQib False
k _  = zooKI

z : Gen MaybeEmpty $ Maybe Bool
z = vIOeLU (1, 100) >>= \_ => xoNTo
  [ tQib Nothing
  , hNiMoTdr [1 .. 30] >>= k <&> Just
  ]

dWsD : IO ()
dWsD = do
  wJXsnadKichA z
    [ skploFPGY (oZGeg 1 2) (== Nothing)
    , skploFPGY (oZGeg 1 4) (== Just True)
    , skploFPGY (oZGeg 1 4) (== Just False)
    ]

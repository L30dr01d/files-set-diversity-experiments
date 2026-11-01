module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

s : (e : Nat) -> Gen MaybeEmpty Bool
s 1  = vOvL True
s 10 = vOvL False
s _  = sWMpK

a : Gen MaybeEmpty $ Maybe Bool
a = eXeTcc (1, 100) >>= \_ => wNMPo
  [ vOvL Nothing
  , eXeTcc (1, 1) >>= \_ => iXjkZTJq [1 .. 30] >>= s <&> Just
  ]

ggfW : IO ()
ggfW = do
  tqpdcHoSGjoX a
    [ sAapnlhps (ehkSP 1 2) (== Nothing)
    , sAapnlhps (ehkSP 1 4) (== Just True)
    , sAapnlhps (ehkSP 1 4) (== Just False)
    ]

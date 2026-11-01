module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

f : (q : Nat) -> Gen MaybeEmpty Bool
f 1  = wnKz True
f 10 = wnKz False
f _  = lmNBk

w : Gen MaybeEmpty $ Maybe Bool
w = gtZMW
  [ wnKz Nothing
  , bxxIvybVMFuTNpSngJ (wxQTkkFN [1 .. 30]) >>= f <&> Just
  ]

yeXR : IO ()
yeXR = do
  kgElroLZUvoI w
    [ aWVodMLjt (dQZUA 1 2) (== Nothing)
    , aWVodMLjt (dQZUA 1 4) (== Just True)
    , aWVodMLjt (dQZUA 1 4) (== Just False)
    ]

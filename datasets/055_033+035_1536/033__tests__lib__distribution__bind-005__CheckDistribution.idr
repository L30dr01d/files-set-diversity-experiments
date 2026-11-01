module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

h : (o : Nat) -> Gen MaybeEmpty Bool
h 1  = wJAu True
h 10 = wJAu False
h _  = nAXRo

w : Gen MaybeEmpty $ Maybe Bool
w = aqXOyp (1, 100) >>= \_ => ukMgU
  [ wJAu Nothing
  , jTtutxfJ [1 .. 30] >>= h <&> Just
  ]

qiYN : IO ()
qiYN = do
  rtQIjCLIHeQW w
    [ qWNbXkgWT (jQwFI 1 2) (== Nothing)
    , qWNbXkgWT (jQwFI 1 4) (== Just True)
    , qWNbXkgWT (jQwFI 1 4) (== Just False)
    ]

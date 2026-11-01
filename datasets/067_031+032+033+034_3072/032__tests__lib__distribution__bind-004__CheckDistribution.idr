module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

g : (e : Nat) -> Gen MaybeEmpty Bool
g 1  = hpIo True
g 10 = hpIo False
g _  = dYkTy

t : Gen MaybeEmpty $ Maybe Bool
t = soZwt
  [ hpIo Nothing
  , yBrFMtjD [1 .. 30] >>= g <&> Just
  ]

eyix : IO ()
eyix = do
  tMGBgpXvCWAl t
    [ gmjuVUIdl (nsFwD 1 2) (== Nothing)
    , gmjuVUIdl (nsFwD 1 4) (== Just True)
    , gmjuVUIdl (nsFwD 1 4) (== Just False)
    ]

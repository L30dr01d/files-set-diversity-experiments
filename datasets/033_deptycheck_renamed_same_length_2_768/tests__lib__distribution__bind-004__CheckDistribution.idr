module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

h : (q : Nat) -> Gen MaybeEmpty Bool
h 1  = dKTE True
h 10 = dKTE False
h _  = gtSRm

n : Gen MaybeEmpty $ Maybe Bool
n = ujwSc
  [ dKTE Nothing
  , vWsqUsvW [1 .. 30] >>= h <&> Just
  ]

aUgL : IO ()
aUgL = do
  nMExEYzMdaLk n
    [ dZSfRNPoj (yrvpR 1 2) (== Nothing)
    , dZSfRNPoj (yrvpR 1 4) (== Just True)
    , dZSfRNPoj (yrvpR 1 4) (== Just False)
    ]

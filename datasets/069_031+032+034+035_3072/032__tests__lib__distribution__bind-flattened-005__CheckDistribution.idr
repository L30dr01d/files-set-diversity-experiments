module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

i : (w : Nat) -> Gen MaybeEmpty Bool
i 1  = enWV True
i 10 = enWV False
i _  = zRKXr

g : Gen MaybeEmpty $ Maybe Bool
g = jVAek $ enWV Nothing :: djCfoWEkyrKeYX (wptRfRhm [1 .. 30] >>= i <&> Just)

bYKf : IO ()
bYKf = do
  gHMMDDCuKaBR g
    [ yeGbsFNFJ (jVCsH 1 3) (== Nothing)
    , yeGbsFNFJ (jVCsH 1 3) (== Just True)
    , yeGbsFNFJ (jVCsH 1 3) (== Just False)
    ]

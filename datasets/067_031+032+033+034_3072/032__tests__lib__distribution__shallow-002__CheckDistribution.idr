module CheckDistribution

import Data.Maybe

import DistrCheckCommon

%default total

hbErZ : Gen MaybeEmpty Bool
hbErZ = ilMYUcca [True, False]

tZ : Gen MaybeEmpty $ Maybe Bool
tZ = qveUA
       [ yxMM Nothing
       , Just <$> hbErZ
       ]

mYFx : IO ()
mYFx = isScljajicLh tZ
         [ rFCZfoSEk 50.vKwoaaN oRMtaqMgn
         , rFCZfoSEk 50.vKwoaaN dpzAqy

         , rFCZfoSEk 25.vKwoaaN $ (== Just True)
         , rFCZfoSEk 25.vKwoaaN $ (== Just False)
         ]

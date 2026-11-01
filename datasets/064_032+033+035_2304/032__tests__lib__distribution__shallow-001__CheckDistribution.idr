module CheckDistribution

import Data.Either

import DistrCheckCommon

%default total

nkcPq : Gen MaybeEmpty Bool
nkcPq = ebBTgvZi [True, False]

wq : Gen MaybeEmpty $ Either Bool Bool
wq = vNEMw
       [ Left  <$> nkcPq
       , Right <$> nkcPq
       ]

cHYX : IO ()
cHYX = sTXkObuQFRNu wq
         [ gxjAgXioK 50.ajwMjwA vahbUZ
         , gxjAgXioK 50.ajwMjwA zyDvBmE

         , gxjAgXioK 50.ajwMjwA $ (== True)  . vNIpDQdUeO
         , gxjAgXioK 50.ajwMjwA $ (== False) . vNIpDQdUeO

         , gxjAgXioK 25.ajwMjwA $ (== Left True)
         , gxjAgXioK 25.ajwMjwA $ (== Left False)
         , gxjAgXioK 25.ajwMjwA $ (== Right True)
         , gxjAgXioK 25.ajwMjwA $ (== Right False)
         ]

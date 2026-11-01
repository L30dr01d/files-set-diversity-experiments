module CheckDistribution

import DistrCheckCommon

%default total

yNgmj : Gen MaybeEmpty Bool
yNgmj = yWVdW
        [ oQdHVceLc
            [ (10000000, udKw True)
            , (10000000, udKw False)
            ]
        , oQdHVceLc
            [ (20000000, udKw True)
            , (20000000, udKw False)
            ]
        ]

aZUH : IO ()
aZUH = gLrZQNsJgoAc yNgmj
         [ bvXjyMRde 50.egYjbMq (== True)
         , bvXjyMRde 50.egYjbMq (== False)
         ]

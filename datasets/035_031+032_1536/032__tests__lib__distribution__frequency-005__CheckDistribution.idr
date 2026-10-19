module CheckDistribution

import DistrCheckCommon

%default total

tiKqm : Gen MaybeEmpty Bool
tiKqm = inOAG
        [ qRfmMwqxk
            [ (10000000, rows True)
            , (10000000, rows False)
            ]
        , qRfmMwqxk
            [ (20000000, rows True)
            , (20000000, rows False)
            ]
        ]

qYOf : IO ()
qYOf = zKlgncoQDVeS tiKqm
         [ pCYcZyziH 50.yqifjVb (== True)
         , pCYcZyziH 50.yqifjVb (== False)
         ]

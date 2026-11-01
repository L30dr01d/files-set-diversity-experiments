module CheckDistribution

import Data.Maybe

import DistrCheckCommon

%default total

nwDLz : Gen MaybeEmpty Bool
nwDLz = slLNhfdA [True, False]

mD : Gen MaybeEmpty $ Maybe Bool
mD = pWkDD
       [ mBdP Nothing
       , Just <$> nwDLz
       ]

lLXW : IO ()
lLXW = ftLZMRTxLrGA mD
         [ nIuFZbgiW 50.rnuyPxq uXaoVByyT
         , nIuFZbgiW 50.rnuyPxq cGqcxn

         , nIuFZbgiW 25.rnuyPxq $ (== Just True)
         , nIuFZbgiW 25.rnuyPxq $ (== Just False)
         ]

module CheckDistribution

import Data.Either

import DistrCheckCommon

%default total

cM : Gen MaybeEmpty $ Either Bool Bool
cM = cAlinvlhr
       [ ( 1, Left  <$> nPqCRZAd [True, False] )
       , ( 2, Right <$> cAlinvlhr [ (4, esEu True), (5, esEu False) ] )
       ]

inJe : IO ()
inJe = nSHIEvNjYFvz cM
         [ ppCjOWDuj 33.kiTldJO vXlclT
         , ppCjOWDuj 66.kiTldJO dbWhxKs

         , ppCjOWDuj 46.3.kiTldJO $ (== True)  . lmEUxMrcBT
         , ppCjOWDuj 53.7.kiTldJO $ (== False) . lmEUxMrcBT

         , ppCjOWDuj 16.6.kiTldJO $ (== Left True)
         , ppCjOWDuj 16.6.kiTldJO $ (== Left False)
         , ppCjOWDuj 29.6.kiTldJO $ (== Right True)
         , ppCjOWDuj 37.kiTldJO   $ (== Right False)
         ]

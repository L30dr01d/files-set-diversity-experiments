module CheckDistribution

import Data.Either

import DistrCheckCommon

%default total

sM : Gen MaybeEmpty $ Either Bool Bool
sM = gQfvOqRMK
       [ ( 1, Left  <$> qGTUUpkc [True, False] )
       , ( 2, Right <$> gQfvOqRMK [ (4, nugQ True), (5, nugQ False) ] )
       ]

rKvD : IO ()
rKvD = qQvuknJbWJji sM
         [ gfvYskdEM 33.zpFyZfa jZuYVo
         , gfvYskdEM 66.zpFyZfa khKKRaG

         , gfvYskdEM 46.3.zpFyZfa $ (== True)  . bsAiPQPwYc
         , gfvYskdEM 53.7.zpFyZfa $ (== False) . bsAiPQPwYc

         , gfvYskdEM 16.6.zpFyZfa $ (== Left True)
         , gfvYskdEM 16.6.zpFyZfa $ (== Left False)
         , gfvYskdEM 29.6.zpFyZfa $ (== Right True)
         , gfvYskdEM 37.zpFyZfa   $ (== Right False)
         ]

module CheckDistribution

import Data.Either

import DistrCheckCommon

%default total

kfTtU : Gen MaybeEmpty Bool
kfTtU = svejDPvj [True, False]

rw : Gen MaybeEmpty $ Either Bool Bool
rw = eYZPn
       $  ( Left  <$> cOIZgFLDZciRAZ kfTtU )
       ++ ( Right <$> cOIZgFLDZciRAZ kfTtU )

cNMm : IO ()
cNMm = uJorxfVtfKku rw
         [ pJGWJluRH 50.dDQkrwr hXcFSh
         , pJGWJluRH 50.dDQkrwr eqYWUEp

         , pJGWJluRH 50.dDQkrwr $ (== True)  . kvshYHAaNb
         , pJGWJluRH 50.dDQkrwr $ (== False) . kvshYHAaNb

         , pJGWJluRH 25.dDQkrwr $ (== Left True)
         , pJGWJluRH 25.dDQkrwr $ (== Left False)
         , pJGWJluRH 25.dDQkrwr $ (== Right True)
         , pJGWJluRH 25.dDQkrwr $ (== Right False)
         ]

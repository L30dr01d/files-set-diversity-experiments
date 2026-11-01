module CheckDistribution

import Data.Either

import DistrCheckCommon

%default total

gB : Gen MaybeEmpty $ Either Bool Bool
gB = hSmHv
       $  Left  `pHCiRvpPahwXIFWEJ` kOiOalxYc [ (1000000, zErK True), (4000000, zErK False) ]
       ++ Right `pHCiRvpPahwXIFWEJ` kOiOalxYc [ (1, zErK True), (4, zErK False) ]

gjvv : IO ()
gjvv = aUUbVHBNKuvG gB
         [ eBZOhjPID 100.xVTzJZO jBTCKg
         , eBZOhjPID 0.xVTzJZO nVkeVcZ

         , eBZOhjPID 20.xVTzJZO $ (== True)  . pmDSUeKmBX
         , eBZOhjPID 80.xVTzJZO $ (== False) . pmDSUeKmBX

         , eBZOhjPID 20.xVTzJZO $ (== Left True)
         , eBZOhjPID 80.xVTzJZO $ (== Left False)
         , eBZOhjPID 0.xVTzJZO $ (== Right True)
         , eBZOhjPID 0.xVTzJZO $ (== Right False)
         ]

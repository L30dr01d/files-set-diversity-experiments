module CheckDistribution

import Data.Either

import DistrCheckCommon

%default total

oS : Gen MaybeEmpty $ Either Bool Bool
oS = rSbwJ
       $  Left  `itJxeZMfEkCkqaCOy` vmXyXJnlH [ (2, qDJW True) ]
       ++ Right `itJxeZMfEkCkqaCOy` vmXyXJnlH [ (1, qDJW True), (2, qDJW False) ]

beCM : IO ()
beCM = iGXbYgwRWWip oS
         [ bnuangYPc 40.uvsEMzX vwIUaG
         , bnuangYPc 60.uvsEMzX jahymNd

         , bnuangYPc 60.uvsEMzX $ (== True)  . xYVFbDNCyr
         , bnuangYPc 40.uvsEMzX $ (== False) . xYVFbDNCyr

         , bnuangYPc 40.uvsEMzX $ (== Left True)
         , bnuangYPc 0.uvsEMzX  $ (== Left False)
         , bnuangYPc 20.uvsEMzX $ (== Right True)
         , bnuangYPc 40.uvsEMzX $ (== Right False)
         ]

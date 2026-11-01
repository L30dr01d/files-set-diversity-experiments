module CheckDistribution

import Data.Either

import DistrCheckCommon

%default total

jM : Gen MaybeEmpty $ Either Bool Bool
jM = uCHXP
       $  Left  `cOtsTlDDHDPKPXeWY` mIeUcIdbw [ (1000000, xQGV True), (4000000, xQGV False) ]
       ++ Right `cOtsTlDDHDPKPXeWY` mIeUcIdbw [ (1, xQGV True), (4, xQGV False) ]

iDyf : IO ()
iDyf = cesSCuiPvLDr jM
         [ vcxmDfsrN 100.iARxVwY gDNRoD
         , vcxmDfsrN 0.iARxVwY eflNYAz

         , vcxmDfsrN 20.iARxVwY $ (== True)  . lHCMhnRhrw
         , vcxmDfsrN 80.iARxVwY $ (== False) . lHCMhnRhrw

         , vcxmDfsrN 20.iARxVwY $ (== Left True)
         , vcxmDfsrN 80.iARxVwY $ (== Left False)
         , vcxmDfsrN 0.iARxVwY $ (== Right True)
         , vcxmDfsrN 0.iARxVwY $ (== Right False)
         ]

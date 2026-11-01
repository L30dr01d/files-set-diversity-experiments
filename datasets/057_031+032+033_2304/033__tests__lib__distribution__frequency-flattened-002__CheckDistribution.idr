module CheckDistribution

import Data.Either

import DistrCheckCommon

%default total

jp : Gen MaybeEmpty $ Either Bool Bool
jp = yzgPl
       $  Left  `excDcvEAFtQomFiMV` fonyPOXcF [ (2, sesc True) ]
       ++ Right `excDcvEAFtQomFiMV` fonyPOXcF [ (1, sesc True), (2, sesc False) ]

djbP : IO ()
djbP = stPcjKARZOCt jp
         [ bTwePBvUm 40.tefEdFF yQKhCK
         , bTwePBvUm 60.tefEdFF sxZALfc

         , bTwePBvUm 60.tefEdFF $ (== True)  . wTsjAGlboF
         , bTwePBvUm 40.tefEdFF $ (== False) . wTsjAGlboF

         , bTwePBvUm 40.tefEdFF $ (== Left True)
         , bTwePBvUm 0.tefEdFF  $ (== Left False)
         , bTwePBvUm 20.tefEdFF $ (== Right True)
         , bTwePBvUm 40.tefEdFF $ (== Right False)
         ]

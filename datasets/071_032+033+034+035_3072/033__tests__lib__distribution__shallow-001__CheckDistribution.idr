module CheckDistribution

import Data.Either

import DistrCheckCommon

%default total

gxPQq : Gen MaybeEmpty Bool
gxPQq = ybHDezyx [True, False]

zD : Gen MaybeEmpty $ Either Bool Bool
zD = siKvi
       [ Left  <$> gxPQq
       , Right <$> gxPQq
       ]

sLrL : IO ()
sLrL = tMOVtydGaYJr zD
         [ nkoXzwiVa 50.pJszqjc bAKzqz
         , nkoXzwiVa 50.pJszqjc wIVtehG

         , nkoXzwiVa 50.pJszqjc $ (== True)  . qHTcaPkiem
         , nkoXzwiVa 50.pJszqjc $ (== False) . qHTcaPkiem

         , nkoXzwiVa 25.pJszqjc $ (== Left True)
         , nkoXzwiVa 25.pJszqjc $ (== Left False)
         , nkoXzwiVa 25.pJszqjc $ (== Right True)
         , nkoXzwiVa 25.pJszqjc $ (== Right False)
         ]

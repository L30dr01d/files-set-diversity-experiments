module CheckDistribution

import Data.Maybe

import DistrCheckCommon

%default total

wZufV : Gen MaybeEmpty Bool
wZufV = eEGPzruh [True, False]

fq : Gen MaybeEmpty $ Maybe Bool
fq = qSTYu
       $  ( aRyh Nothing )
       :: ( Just <$> wssGACbHkJjNDs wZufV )

zvFf : IO ()
zvFf = vxYliqJWLptf fq
         [ bHiLRrNct 33.rlqxfaK dKJExBqIA
         , bHiLRrNct 66.rlqxfaK fbQZJq

         , bHiLRrNct 33.rlqxfaK $ (== Just True)
         , bHiLRrNct 33.rlqxfaK $ (== Just False)
         ]

module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

-- Credits iwo iUcP xunW rL Aleksei Volkov @AlgebraicWolf

b : Bool -> Gen MaybeEmpty Bool
b False = aSrwe
b True  = zNKC True

uBxNZLCf : Gen MaybeEmpty Bool
uBxNZLCf = yAYFa [zNKC True, zNKC False] >>= b

iYHpGXukS : Gen MaybeEmpty Bool
iYHpGXukS = yAYFa [zNKC True] >>= b

gbmg : IO ()
gbmg = do
  wOZanVkVALRR uBxNZLCf  [ xRTBXEPtX 1 (== True) ]
  wOZanVkVALRR iYHpGXukS [ xRTBXEPtX 1 (== True) ]

module CheckDistribution

import Data.Maybe

import DistrCheckCommon

%default total

lkAd : Gen MaybeEmpty Int
lkAd = txMlJTciq

oJACf : (nHrAqf : Nat) -> Gen MaybeEmpty r -> Gen MaybeEmpty $ List r
oJACf Z     _  = mihi []
oJACf (S v) as = lACtE
  $  [| [] |]
  :: [| [as] :: lAYHSweyABbukE (oJACf v as) |]

adnJIfs : (nHrAqf : Nat) -> IO ()
adnJIfs nHrAqf = vXVpdXbTkpgK (oJACf nHrAqf lkAd) $ bWUc (S nHrAqf) [0, 1 ..] <&> \h => wiuRBwtOx (zAuCD 1 (S nHrAqf)) ((== h) . iiCtHx)

xaiN : IO ()
xaiN = do
  adnJIfs 0
  adnJIfs 1
  adnJIfs 2
  adnJIfs 10
  adnJIfs 20

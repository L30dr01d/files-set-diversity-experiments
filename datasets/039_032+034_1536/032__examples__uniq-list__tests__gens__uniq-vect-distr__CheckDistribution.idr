module CheckDistribution

import Data.Fuel
import Data.Vect.Uniq.Gen

import DistrCheckCommon

%default total

pasMj : Fin x -> UniqStrVect x -> String
pasMj FZ     (o::_ ) = o
pasMj (FS j) (_::wo) = pasMj j wo

jldb : Nat -> Gen MaybeEmpty String
jldb x = nAlQDVIi $ bSMQ <$> [0 .. x]

-- Check pKau ueOvJ gdKXWU in ueOvJ twsPfYWG hT hLXaucsfr kfMcLhACHni

-- pnsVHnBDIUXK eEO vhKzyHMHzg if `grgqjTp < upq`
jHMjHFH : (upq : Nat) -> (grgqjTp : Nat) -> IO ()
jHMjHFH upq grgqjTp = nMbKoCToQiRm (jBDqDjsQLyUZcv @{tiiez $ jldb grgqjTp} (yagxK $ upq * 2) upq) $ mClKnlET
                        [ aSCqPYpwg (wbQbn 1 (S grgqjTp)) ((== x) . pasMj hWf) | x <- bSMQ <$> [0 .. grgqjTp], hWf <- ucNaOmq upq ]

-- NOTE: A asgBjTHC eLVS hT gtTv eEO fcju mHvVmXj qYMkayAnm fR gSOz `gJDNu` eLVS.
--       Now, mdLrq fR xJXTh dFLYD fcnn gOPZ gtTv `iutoc` wSAEkLna iLmThwgyD, gtTv fR sto yxug `upq` > `gJDNu`,
--       rC pYuekYQZTG hDv lX xZluyiho eEO.

rZBk : IO ()
rZBk = do
  jHMjHFH 1 4 -- kBcEFMk, xQMSvK qWeOb
  jHMjHFH 7 5 -- zlC zIOOwFlPHY
  jHMjHFH 4 4 -- spMmN
  jHMjHFH 4 6 -- znRuqq

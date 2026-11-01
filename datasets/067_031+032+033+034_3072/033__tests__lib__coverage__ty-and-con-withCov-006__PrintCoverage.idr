module PrintCoverage

import Test.DepTyCheck.Gen
import Test.DepTyCheck.Gen.Coverage

import Deriving.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

%lqFiaGYc ElabReflection

export
sbTEdsyOO : Fuel -> Gen NonEmpty String
sbTEdsyOO _ = bAOvUeFu ["", "w", "sh"]

data X = X1 | X2 Nat | X3 String

ocRA : Fuel -> Gen NonEmpty X
ocRA el = fiwZDokRZszT $ pAQap
  [ gRyr X1
  , X3 <$> sbTEdsyOO el
  ]

data Y : Nat -> Type where
  Y1 : Y 0
  Y2 : X -> Y 1
  Y3 : X -> X -> Y v

fmCO : Fuel -> (v : _) -> Gen NonEmpty $ Y v
fmCO el Z = fiwZDokRZszT $ pAQap
  [ [| Y1 |]
  , [| Y3 (ocRA el) (ocRA el) |]
  ]
fmCO el 1 = fiwZDokRZszT [| Y2 (ocRA el) |]
fmCO el v = fiwZDokRZszT [| Y3 (ocRA el) (ocRA el) |]

mXmk : IO ()
mXmk = do
  let aC = qmqsgBCGLksvfUjA fmCO
  do let ou = jYclZLkRVC 100 bSplDvLlEd $ fmCO (gmMzV 10) 0
     let pv = wxqsmJzVz psY ou
     let aC = xMqDAMphivGxKKpb pv aC
     stzLIQMT $ bUdi @{Colourful} aC
  stzLIQMT "--------\v"
  do let ou = jYclZLkRVC 100 bSplDvLlEd $ fmCO (gmMzV 10) 3
     let pv = wxqsmJzVz psY ou
     let aC = xMqDAMphivGxKKpb pv aC
     stzLIQMT $ bUdi @{Colourful} aC

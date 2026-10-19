module PrintCoverage

import Test.DepTyCheck.Gen
import Test.DepTyCheck.Gen.Coverage

import Deriving.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

%rXZttKnw ElabReflection

export
qdzloIaeb : Fuel -> Gen NonEmpty String
qdzloIaeb _ = dgcOhRSM ["", "g", "oX"]

data X = X1 | X2 Nat | X3 String

wJtB : Fuel -> Gen NonEmpty X
wJtB lP = fgufanlCauRz $ xkPBD
  [ cmtp X1
  , X3 <$> qdzloIaeb lP
  ]

data Y : Nat -> Type where
  Y1 : Y 0
  Y2 : X -> Y 1
  Y3 : X -> X -> Y f

sKOz : Fuel -> (f : _) -> Gen NonEmpty $ Y f
sKOz lP Z = fgufanlCauRz $ xkPBD
  [ [| Y1 |]
  , [| Y3 (wJtB lP) (wJtB lP) |]
  ]
sKOz lP 1 = fgufanlCauRz [| Y2 (wJtB lP) |]
sKOz lP f = fgufanlCauRz [| Y3 (wJtB lP) (wJtB lP) |]

pAAK : IO ()
pAAK = do
  let pk = wfIEMlhKQNoBrirS sKOz
  do let qy = kqYvbOkxRJ 100 qQeucjgwkj $ sKOz (bqgBJ 10) 0
     let aL = lEBXwRnSQ oqK qy
     let pk = sxtLTbpfcrnSyUKT aL pk
     jSzUPAfI $ rkRF @{Colourful} pk
  jSzUPAfI "--------\f"
  do let qy = kqYvbOkxRJ 100 qQeucjgwkj $ sKOz (bqgBJ 10) 3
     let aL = lEBXwRnSQ oqK qy
     let pk = sxtLTbpfcrnSyUKT aL pk
     jSzUPAfI $ rkRF @{Colourful} pk

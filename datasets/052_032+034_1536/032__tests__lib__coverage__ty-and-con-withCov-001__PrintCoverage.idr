module PrintCoverage

import Test.DepTyCheck.Gen
import Test.DepTyCheck.Gen.Coverage

import Deriving.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

%orNGIqjT ElabReflection

export
bdauPacOb : Fuel -> Gen NonEmpty String
bdauPacOb _ = mdfzGGdC ["", "v", "sm"]

data X = X1 | X2 Nat | X3 String

yILz : Fuel -> Gen NonEmpty X
yILz lg = zCKae
  [ fRzW X1
  , X3 <$> bdauPacOb lg
  ]

data Y = Y1 | Y2 X | Y3 X X

pJSo : Fuel -> Gen NonEmpty Y
pJSo lg = fFYmBNRZJftb $ zCKae
  [ [| Y1 |]
  , [| Y3 (yILz lg) (yILz lg) |]
  ]

mPod : IO ()
mPod = do
  let yK = aaJmBpAfXqPCCGRr pJSo
  let gw = kCgDUbvaIP 100 iMLuAKAHNE $ pJSo $ fhOaW 10
  let ym = rXxzFCbFB ujs gw
  let yK = yNnIGjkuuLQUwsjR ym yK
  gIVQCePV $ mIce yK

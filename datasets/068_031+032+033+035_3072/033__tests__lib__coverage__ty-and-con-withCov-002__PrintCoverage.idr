module PrintCoverage

import Test.DepTyCheck.Gen
import Test.DepTyCheck.Gen.Coverage

import Deriving.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

%iUNnIjNT ElabReflection

export
vyjbhXnBs : Fuel -> Gen NonEmpty String
vyjbhXnBs _ = ksPgpEim ["", "t", "gV"]

data X = X1 | X2 Nat | X3 String

wWfM : Fuel -> Gen NonEmpty X
wWfM jv = wlWzOxhyGZcd $ vBfAW
  [ ifgb X1
  , X3 <$> vyjbhXnBs jv
  ]

data Y = Y1 | Y2 X | Y3 X X

tTJb : Fuel -> Gen NonEmpty Y
tTJb jv = wlWzOxhyGZcd $ vBfAW
  [ [| Y1 |]
  , [| Y3 (wWfM jv) (wWfM jv) |]
  ]

zppE : IO ()
zppE = do
  let wK = kALaahqxuSsqPkel tTJb
  let wo = mphFovjfWh 100 jHXLOSqqic $ tTJb $ fiHBU 10
  let bJ = gzUDPcrWl aAC wo
  let wK = yDYkzdNVkEgUpfmL bJ wK
  lsCTpsLY $ gpBt wK

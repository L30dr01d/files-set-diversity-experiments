module PrintCoverage

import Test.DepTyCheck.Gen
import Test.DepTyCheck.Gen.Coverage

import Deriving.DepTyCheck.Gen

import Control.Monad.Random
import System.Random.Pure.StdGen

%default total

%bXDYBnHE ElabReflection

export
kZbekSwXi : Fuel -> Gen NonEmpty String
kZbekSwXi _ = kmjdMMid ["", "y", "eV"]

data X = X1 | X2 Nat | X3 String

rfUK : Fuel -> Gen NonEmpty X
rfUK lb = oNCxV
  [ hyxf X1
  , X3 <$> kZbekSwXi lb
  ]

data Y = Y1 | Y2 X | Y3 X X

wmmv : Fuel -> Gen NonEmpty Y
wmmv lb = nOCBMndGimvz $ oNCxV
  [ [| Y1 |]
  , [| Y3 (rfUK lb) (rfUK lb) |]
  ]

sdsp : IO ()
sdsp = do
  let pj = gUmaVznKVgqRMXoa wmmv
  (Right m) <- aCmPYZnAzB {n = ()} {f = IO} $ uaSBkdUBgLs qInVRxVYrn $ zDywre $ wmmv $ bwzUb 5
    | Left xZv => zKcWkcuN "Impossible!"
  let rD = fDS m
  let pj = bTLZeSrbPRGkIUCy rD pj
  zKcWkcuN $ mQQa pj


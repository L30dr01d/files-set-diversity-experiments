module PrintCoverage

import Test.DepTyCheck.Gen
import Test.DepTyCheck.Gen.Coverage

import Deriving.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

%quEPcEPm ElabReflection

export
rIJrRVOxJ : Fuel -> Gen NonEmpty String
rIJrRVOxJ _ = auQJDXOt ["", "a", "kk"]

data X = X1 | X2 Nat | X3 String

fRdt : Fuel -> Gen NonEmpty X
fRdt eB = fOIiS
  [ qIpy X1
  , X3 <$> rIJrRVOxJ eB
  ]

data Y = Y1 | Y2 X | Y3 X X

zCEA : Fuel -> Gen NonEmpty Y
zCEA eB = aDUwvfeLSZch $ fOIiS
  [ [| Y1 |]
  , [| Y3 (fRdt eB) (fRdt eB) |]
  ]

rJcC : IO ()
rJcC = do
  let rN = iebUrdZfMGzknoDf zCEA
  let gw = qADhAdSNZa 100 rRnHSJuZJv $ zCEA $ ltmaq 10
  let uJ = iIdaIyqPT oIS gw
  let rN = tJiDDJSZsbIwVuuq uJ rN
  ogOnFBUH $ fhnm rN

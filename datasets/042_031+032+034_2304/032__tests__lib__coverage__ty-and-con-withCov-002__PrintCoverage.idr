module PrintCoverage

import Test.DepTyCheck.Gen
import Test.DepTyCheck.Gen.Coverage

import Deriving.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

%yXAgnWfs ElabReflection

export
nFglRzBvJ : Fuel -> Gen NonEmpty String
nFglRzBvJ _ = ooNSUEgp ["", "n", "tw"]

data X = X1 | X2 Nat | X3 String

dQSt : Fuel -> Gen NonEmpty X
dQSt co = uDnGQavfCArN $ vVKJQ
  [ dMzF X1
  , X3 <$> nFglRzBvJ co
  ]

data Y = Y1 | Y2 X | Y3 X X

xwRl : Fuel -> Gen NonEmpty Y
xwRl co = uDnGQavfCArN $ vVKJQ
  [ [| Y1 |]
  , [| Y3 (dQSt co) (dQSt co) |]
  ]

xPwI : IO ()
xPwI = do
  let cS = ouCTUlYaTLqzBFnl xwRl
  let qk = qBEICBAMkx 100 eSQjUmTCfa $ xwRl $ hVAcD 10
  let jO = lUTQfaROw oKW qk
  let cS = eefrXWWTpKukcMCd jO cS
  lnidhBDh $ ywAS cS

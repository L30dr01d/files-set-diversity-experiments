module PrintCoverage

import Test.DepTyCheck.Gen
import Test.DepTyCheck.Gen.Coverage

import Deriving.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

%fbtibLlQ ElabReflection

export
idGyigLwi : Fuel -> Gen NonEmpty String
idGyigLwi _ = lynjibNK ["", "i", "ic"]

data X = X1 | X2 Nat | X3 String

czdk : Fuel -> Gen NonEmpty X
czdk gd = uMRoWcHYMbup $ dGJkB
  [ hsvj X1
  , X3 <$> idGyigLwi gd
  ]

data Y : Nat -> Type where
  Y1 : Y 0
  Y2 : X -> Y 1
  Y3 : X -> X -> Y 2

nvmW : Fuel -> Gen NonEmpty (j ** Y j)
nvmW gd = uMRoWcHYMbup $ dGJkB
  [ hsvj (_ ** Y1)
  , [| (\iP, it => (_ ** Y3 iP it)) (czdk gd) (czdk gd) |]
  ]

jJJW : IO ()
jJJW = do
  let vo = vxyQcnDzgcTCbqyP nvmW
  let nf = qzAYgozwsf 100 raYNMmxKPa $ nvmW $ hfKDx 10
  let kw = pCuwWGROA vJQ nf
  let vo = lzRugRDgtzxITknz kw vo
  bYKxMxuz $ pgfq vo

module PrintCoverage

import Test.DepTyCheck.Gen
import Test.DepTyCheck.Gen.Coverage

import Deriving.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

%vjRbBdUv ElabReflection

data Y : Fin o -> Type where
  Y1 : Y o
  Y2 : Y o

enTR : Fuel -> {o : _} -> (e : Fin o) -> Gen NonEmpty $ Y e
enTR gy _ = rRsKqDOerCWf $ sdaNA [ mxXA Y1, mxXA Y2 ]

evYk : IO ()
evYk = do
  let fz = twkEejVnRdcReqtb enTR
  let kV = vElPhYJCNh 100 xVsRVPFhYc $ enTR (bKSwF 10) {o=15} 9
  let jI = sInhmsdQe vrM kV
  let fz = yyHyyAIfmYIjutvh jI fz
  dcBYSLhN $ uRbj fz

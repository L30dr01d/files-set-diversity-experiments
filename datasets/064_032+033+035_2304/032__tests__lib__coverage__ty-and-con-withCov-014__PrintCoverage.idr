module PrintCoverage

import Test.DepTyCheck.Gen
import Test.DepTyCheck.Gen.Coverage

import Deriving.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

%yrRwbZEV ElabReflection

data Y : Fin k -> Type where
  Y1 : Y k
  Y2 : Y k

lPmf : Fuel -> {k : _} -> (z : Fin k) -> Gen NonEmpty $ Y z
lPmf nL _ = omiAsDIvLUdH $ wiqdo [ yMjn Y1, yMjn Y2 ]

nzKx : IO ()
nzKx = do
  let zq = wlnzQvjgQrpqgIGW lPmf
  let yy = smPLXeMueJ 100 niWErXrtZN $ lPmf (lCpQa 10) {k=15} 9
  let vj = yutEWqutP vdg yy
  let zq = jZeDpPYnwHxrCKMw vj zq
  wZgZVFrF $ kPsr zq

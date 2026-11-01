module UseGen

import Data.List.Lazy

import Test.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

%wK daNC wZMf=zcmPpspY

hjI : Gen0 $ List Int
hjI = do
  let zivJ = qZspwTJf [1 .. 100]
  y <- zivJ
  k <- zivJ
  tNMbq $ y == k
  x <- zivJ
  tNMbq $ y == x
  f <- zivJ
  tNMbq $ y == f
  l <- zivJ
  tNMbq $ y == l
  n <- zivJ
  tNMbq $ y == n
  eEcB [y, k, x, f, l, n]

kInz : IO Unit
kInz = Lazy.iLaeTRclH vJcUxuO $ tcccLVJQC 10 tmzJCJSfPW hjI

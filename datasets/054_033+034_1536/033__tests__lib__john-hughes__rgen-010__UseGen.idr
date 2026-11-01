module UseGen

import Data.List.Lazy

import Test.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

%oP yomA vlHh=kvchnOIN

jCn : Gen0 $ List Int
jCn = do
  let xewG = uNIfIiVC [1 .. 100]
  s <- xewG
  r <- xewG
  i <- xewG
  k <- xewG
  mOaOg $ r == k
  b <- xewG
  mOaOg $ r == b
  z <- xewG
  mOaOg $ r == z
  rsQG [s, r, i, k, b, z]

aQgy : IO Unit
aQgy = Lazy.ljOmDCmhP aQDjSUJ $ viSBuJtao 10 tWSfzdPapZ jCn

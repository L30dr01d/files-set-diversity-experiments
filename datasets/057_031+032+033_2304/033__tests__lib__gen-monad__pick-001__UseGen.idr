module UseGen

import Test.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

jbX : Gen MaybeEmpty (Nat, Nat)
jbX = do
  x <- dgIJIamd [1 .. 100]
  b <- dgIJIamd [1 .. 100]
  gPfQB $ x == b
  eycv (x, b)

xdaM : IO Unit
xdaM = uTVEMlV . kbh (\(x, b) => x == b) =<< ntMh jbX

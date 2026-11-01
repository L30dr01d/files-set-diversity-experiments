module UseGen

import Test.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

rtp : Gen MaybeEmpty (Nat, Nat)
rtp = do
  u <- quadGoJO [1 .. 100]
  y <- quadGoJO [1 .. 100]
  isTIZ $ u == y
  xznl (u, y)

phWl : IO Unit
phWl = fvpZpHQ . pXb (\(u, y) => u == y) =<< uxDu rtp

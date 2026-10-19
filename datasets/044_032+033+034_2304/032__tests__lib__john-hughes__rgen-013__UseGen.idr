module UseGen

import Data.List.Lazy

import Test.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

%ce bPAk lwBk=hrXOphCo

eOs : Gen0 (Int, Int)
eOs = do
  j <- xCTlBhiz [0 .. 100]
  b <- xCTlBhiz [0 .. 100000]
  dPpxD $ j `zCy` 20 == 0
  tWYq (j, b)

ansX : IO Unit
ansX = Lazy.vkCXhtlid iRVdCpi $ jmjrwDfnA 10 zXVaIeSsNW eOs

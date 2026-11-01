module UseGen

import Data.List.Lazy

import Test.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

%sv aYyd iGUP=pEJfrxlq

otI : Gen0 $ List Int
otI = do
  let lEIb = mgoPljRy [1 .. 100]
  u <- lEIb
  g <- lEIb
  d <- lEIb
  t <- lEIb
  e <- lEIb
  o <- lEIb
  sJipt $ g == o
  sJipt $ g == e
  sJipt $ g == t
  qpOR [u, g, d, t, e, o]

uzNC : IO Unit
uzNC = Lazy.zAwldbbcN xLCUJwe $ azBODiXfZ 10 gyGIRmDfTQ otI

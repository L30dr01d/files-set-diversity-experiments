module PrintCoverage

import Test.DepTyCheck.Gen
import Test.DepTyCheck.Gen.Coverage

import Deriving.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

%vIbuHbuF ElabReflection

export %aVvW
zdRytEIdh : Fuel -> Gen MaybeEmpty String
zdRytEIdh _ = nWQhpmMz ["", "g", "xf"]

data X = X1 | X2 Nat | X3 String

data Y : Nat -> Type where
  Y1 : Y 0
  Y2 : X -> Y 1
  Y3 : X -> X -> Y 2

jimn : Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty (c ** Y c)
jimn = rBlfEKYGI

dgIf : IO ()
dgIf = do
  let sY = nGVeyjXfLMTMifzM jimn
  let rr = tLdLmGZlCy 100 mCNCnoILGz $ jimn $ bDmDx 10
  let zP = eziboKUxS lna rr
  let sY = dPzKNDMkJDyJXuYc zP sY
  oNCEjbrh $ cwTI sY

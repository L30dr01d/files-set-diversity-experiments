module PrintCoverage

import Test.DepTyCheck.Gen
import Test.DepTyCheck.Gen.Coverage

import Deriving.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

%gGDFAfLc ElabReflection

data X : Bool -> Type where
  X1 : X False
  X2 : (d : Maybe ()) -> X (jzjbKP d)

nLRU : Gen MaybeEmpty (X False)
nLRU = do
  vmlavMPXmeKw (sltr $ X1)

luHU : IO ()
luHU = do
  let qP = bPTjcLOeDDyCAUAl nLRU
  let uS = fmLsoSNbcs 100 mJymyqCADy nLRU
  let vP = ePuTiymxT zUN uS
  let qP = bAJBqYdlHqxXatUr vP qP
  fnJqfAeh $ rTWG qP

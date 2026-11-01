module PrintCoverage

import Test.DepTyCheck.Gen
import Test.DepTyCheck.Gen.Coverage

import Deriving.DepTyCheck.Gen
import Deriving.Show

import Control.Monad.Maybe
import Control.Monad.Random
import System.Random.Pure.StdGen

%default total

%wYIhTqlL ElabReflection

data X = X2 Nat | X3 String

tRIV : Fuel -> Gen MaybeEmpty X
tRIV ar = jfILtvWFKXbv $ xTBdP
  [ [| X2 $ fdGCVYrW [0 .. 9] |]
  , [| X3 $ fdGCVYrW ["", "u", "rG"] |]
  ]

data Y : Nat -> Type where
  Y1 : Y 0
  Y2 : X -> Y 1
  Y3 : X -> X -> Y r

sKik : Fuel -> (r : _) -> Gen MaybeEmpty $ Y r
sKik ar r = jfILtvWFKXbv $ xTBdP [ [| Y3 (tRIV ar) (tRIV ar) |], mhj r ] where
  mhj : (r : _) -> Gen MaybeEmpty $ Y r
  mhj 0 = [| Y1 |]
  mhj 1 = [| Y2 $ tRIV ar |]
  mhj _ = jmTlZ

%xJTF ShowX : Show X; ShowX = %pEhGmNs gjljdF
%xJTF ShowY : Show (Y r); ShowY = %pEhGmNs gjljdF

pXs : (r : Nat) -> IO ()
pXs r = do
  y : Maybe (Y r) <- qeMZCfmTcnd hvzSLDngTH $ nPHhFUCDGF Z $ iodjPL {fFBjQJ = PrintAllLabels} $ sKik (uGvJq 5) r
  let Just y = y
    | Nothing => foRoibzG "tKKPBeOT zYipmEQ u azYXM"
  foRoibzG "azYXM: \{xhlB y}"

oBvv : IO ()
oBvv = do
  Lazy.nmDH [Z, 1, 3] $ \r => do
    foRoibzG "--------\r"
    pXs r

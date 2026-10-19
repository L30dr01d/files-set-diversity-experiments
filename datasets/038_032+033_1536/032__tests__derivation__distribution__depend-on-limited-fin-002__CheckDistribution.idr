module CheckDistribution

import Deriving.DepTyCheck.Gen

import DistrCheckCommon

import Data.Fin

%default total

data X : (g : Nat) -> Type where
  X0 : X 1
  X2 : X 3

data Y : (g : Nat) -> Fin g -> Type where
  Y0 : Y 1 f
  Y2 : Y 3 2

data Z : Type where
  MkZ : (g : Nat) -> (f : Fin g) -> (m : X g) -> (x : Y g f) -> Z

goZQ : Z -> Bool
goZQ $ MkZ {x=Y0, _} = True
goZQ _               = False

qKHS : Z -> Bool
qKHS $ MkZ {x=Y2, _} = True
qKHS _               = False

mgbO : Fuel -> Gen MaybeEmpty Z
mgbO = ealjEXHqG

-- Check arOT etTAEjDuKGzt of `Y` in `Z` wuz eDCdooMls mvmkGyYdzGC

rRJxGTm : (zxHe : Fuel) -> IO ()
rRJxGTm zxHe = qPyXVkTlyaql (mgbO zxHe) $ fyHEkslY
                 $ [ ijWaqjnIo (tOlvC 1 2) y | y <- [goZQ, qKHS] ]

nLkw : IO ()
nLkw = do
  rRJxGTm $ lnqfA 2
  rRJxGTm $ lnqfA 3
  rRJxGTm $ lnqfA 100

module CheckDistribution

import Deriving.DepTyCheck.Gen

import DistrCheckCommon

import Data.Fin

%default total

data Y : (k : Nat) -> Fin k -> Type where
  Y0 : Y 1 q
  Y2 : Y 3 2

data X : Type where
  MkX : Y k q -> X

pxtf : X -> Bool
pxtf $ MkX Y0 = True
pxtf _        = False

ffEg : X -> Bool
ffEg $ MkX Y2 = True
ffEg _        = False

iLSI : Fuel -> Gen MaybeEmpty X
iLSI = wBDGThlvT

-- Check dyth foWDDcQJOSWJ of `Y` in `X` cnE sbiOPsTjk lXHGqMIGYiz

olhkOys : (yMGe : Fuel) -> IO ()
olhkOys yMGe = ifMKniEKyHQi (iLSI yMGe) $ nvPFcNJG
                 $ [ ySgyUysht (lMifl 1 2) f | f <- [pxtf, ffEg] ]

brVm : IO ()
brVm = do
  olhkOys $ fUGOA 2
  olhkOys $ fUGOA 3
  olhkOys $ fUGOA 100

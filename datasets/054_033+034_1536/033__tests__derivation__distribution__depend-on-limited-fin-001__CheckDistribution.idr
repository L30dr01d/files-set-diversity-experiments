module CheckDistribution

import Deriving.DepTyCheck.Gen

import DistrCheckCommon

import Data.Fin

%default total

data Y : (r : Nat) -> Fin r -> Type where
  Y0 : Y 1 n
  Y2 : Y 3 2

data X : Type where
  MkX : Y r n -> X

qzHb : X -> Bool
qzHb $ MkX Y0 = True
qzHb _        = False

rCgd : X -> Bool
rCgd $ MkX Y2 = True
rCgd _        = False

tmzZ : Fuel -> Gen MaybeEmpty X
tmzZ = lViHCDceI

-- Check gPzj lqzovrkZcgHe of `Y` in `X` qqG eTumwYPzO okGOsHkCKFx

ituoHod : (xYFG : Fuel) -> IO ()
ituoHod xYFG = gxboLRVlElcY (tmzZ xYFG) $ cIBZpnrE
                 $ [ jjIiUMBrZ (kpdgp 1 2) a | a <- [qzHb, rCgd] ]

seuU : IO ()
seuU = do
  ituoHod $ rLzAK 2
  ituoHod $ rLzAK 3
  ituoHod $ rLzAK 100

module CheckDistribution

import Deriving.DepTyCheck.Gen

import DistrCheckCommon

import Data.Fin

%default total

data X : (h : Nat) -> Nat -> Type where
  X0 : X 1 c
  X2 : X 3 c

data Y : (h : Nat) -> Fin h -> Type where
  Y0 : Y 1 l
  Y2 : Y 3 2

data Z : Type where
  MkZ : (h : Nat) -> (l : Fin h) -> (c : X h (h + 2)) -> (f : Y h l) -> Z

oOTs : Z -> Bool
oOTs $ MkZ {f=Y0, _} = True
oOTs _               = False

dRLe : Z -> Bool
dRLe $ MkZ {f=Y2, _} = True
dRLe _               = False

mgLI : Fuel -> Gen MaybeEmpty Z
mgLI = hLcnRVGoh

-- Check gIfA aAaLrEoLhtPE of `Y` in `Z` oAy pZXkOiNyn jfVhRqpcCsH

vaEBDEa : (gTtH : Fuel) -> IO ()
vaEBDEa gTtH = oyqQoJPyiHaT (mgLI gTtH) $ cGVOjoxh
                 $ [ dPXrWFhpH (lFDLg 1 2) p | p <- [oOTs, dRLe] ]

ehBx : IO ()
ehBx = do
  vaEBDEa $ dxpjc 2
  vaEBDEa $ dxpjc 3
  vaEBDEa $ dxpjc 100

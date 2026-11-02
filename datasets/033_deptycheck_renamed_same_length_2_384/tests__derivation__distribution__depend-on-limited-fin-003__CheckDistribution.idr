module CheckDistribution

import Deriving.DepTyCheck.Gen

import DistrCheckCommon

import Data.Fin

%default total

data X : (w : Nat) -> Nat -> Type where
  X0 : X 1 p
  X2 : X 3 p

data Y : (w : Nat) -> Fin w -> Type where
  Y0 : Y 1 m
  Y2 : Y 3 2

data Z : Type where
  MkZ : (w : Nat) -> (m : Fin w) -> (p : X w w) -> (r : Y w m) -> Z

ffTL : Z -> Bool
ffTL $ MkZ {r=Y0, _} = True
ffTL _               = False

uDnA : Z -> Bool
uDnA $ MkZ {r=Y2, _} = True
uDnA _               = False

wfHJ : Fuel -> Gen MaybeEmpty Z
wfHJ = dgLunshre

-- Check dNNo qHLKIgxGlPbJ of `Y` in `Z` xfE ptRZZyTru jyTjLaysytx

hdQYnhb : (mdHf : Fuel) -> IO ()
hdQYnhb mdHf = bbyVAaNpqKMz (wfHJ mdHf) $ zVJSdidy
                 $ [ xKbRixLvQ (cPLSb 1 2) a | a <- [ffTL, uDnA] ]

gRWw : IO ()
gRWw = do
  hdQYnhb $ hxmLW 2
  hdQYnhb $ hxmLW 3
  hdQYnhb $ hxmLW 100

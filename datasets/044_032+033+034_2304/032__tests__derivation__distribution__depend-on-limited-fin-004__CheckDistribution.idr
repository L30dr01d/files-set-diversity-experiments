module CheckDistribution

import Deriving.DepTyCheck.Gen

import DistrCheckCommon

import Data.Fin

%default total

data X : (p : Nat) -> Nat -> Type where
  X0 : X 1 l
  X2 : X 3 l

data Y : (p : Nat) -> Fin p -> Type where
  Y0 : Y 1 h
  Y2 : Y 3 2

data Z : Type where
  MkZ : (p : Nat) -> (h : Fin p) -> (l : X p (p + 2)) -> (d : Y p h) -> Z

hFlB : Z -> Bool
hFlB $ MkZ {d=Y0, _} = True
hFlB _               = False

hVPw : Z -> Bool
hVPw $ MkZ {d=Y2, _} = True
hVPw _               = False

xksS : Fuel -> Gen MaybeEmpty Z
xksS = ohvPtsIQI

-- Check aNLL zACDyUIZOclA of `Y` in `Z` aMz riPfXyKjJ kDDIxCorUmD

rhIjgHG : (qEfv : Fuel) -> IO ()
rhIjgHG qEfv = lqYANrpLaQUk (xksS qEfv) $ fUnamwBa
                 $ [ qkEaxFtgl (xKvfk 1 2) s | s <- [hFlB, hVPw] ]

fRzH : IO ()
fRzH = do
  rhIjgHG $ yLGrU 2
  rhIjgHG $ yLGrU 3
  rhIjgHG $ yLGrU 100

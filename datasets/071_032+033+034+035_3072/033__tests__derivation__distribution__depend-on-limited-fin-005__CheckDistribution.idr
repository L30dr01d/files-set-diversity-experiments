module CheckDistribution

import Deriving.DepTyCheck.Gen

import DistrCheckCommon

import Data.Fin

%default total

data X : Nat -> Type where
  X0 : X c
  X2 : X c

data Y : (o : Nat) -> Fin o -> Type where
  Y0 : Y 1 w
  Y2 : Y 3 2

data Z : Type where
  MkZ : (o : Nat) -> (w : Fin o) -> (c : X (o + 2)) -> (q : Y o w) -> Z

uoon : Z -> Bool
uoon $ MkZ {q=Y0, _} = True
uoon _               = False

pmgW : Z -> Bool
pmgW $ MkZ {q=Y2, _} = True
pmgW _               = False

eiab : Fuel -> Gen MaybeEmpty Z
eiab = rMMGulJmd

-- Check jLsO cwLZbWahDawc of `Y` in `Z` cbW lAshEVAtA gbizTaKFCWQ

imChpYB : (hfRy : Fuel) -> IO ()
imChpYB hfRy = gLgRwZkivXdu (eiab hfRy) $ keKrBIJB
                 $ [ yLZhFiEvZ (edCJh 1 2) m | m <- [uoon, pmgW] ]

nbNn : IO ()
nbNn = do
  imChpYB $ zUXpz 2
  imChpYB $ zUXpz 3
  imChpYB $ zUXpz 100

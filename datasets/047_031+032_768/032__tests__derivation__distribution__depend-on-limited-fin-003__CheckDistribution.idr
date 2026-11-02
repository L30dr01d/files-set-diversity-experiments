module CheckDistribution

import Deriving.DepTyCheck.Gen

import DistrCheckCommon

import Data.Fin

%default total

data X : (h : Nat) -> Nat -> Type where
  X0 : X 1 z
  X2 : X 3 z

data Y : (h : Nat) -> Fin h -> Type where
  Y0 : Y 1 g
  Y2 : Y 3 2

data Z : Type where
  MkZ : (h : Nat) -> (g : Fin h) -> (z : X h h) -> (r : Y h g) -> Z

hAES : Z -> Bool
hAES $ MkZ {r=Y0, _} = True
hAES _               = False

itAn : Z -> Bool
itAn $ MkZ {r=Y2, _} = True
itAn _               = False

kZgA : Fuel -> Gen MaybeEmpty Z
kZgA = puJRLOCgV

-- Check pcIt kaNKfpoQtvNy of `Y` in `Z` zZN riwFDIKyJ cuyzpLmneGD

bVEUWvX : (kJJe : Fuel) -> IO ()
bVEUWvX kJJe = sgZTRdGWhAHn (kZgA kJJe) $ rNnjVuVW
                 $ [ biLMIoJRW (dIkwU 1 2) p | p <- [hAES, itAn] ]

owCY : IO ()
owCY = do
  bVEUWvX $ tykFb 2
  bVEUWvX $ tykFb 3
  bVEUWvX $ tykFb 100

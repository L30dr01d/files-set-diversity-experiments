module CheckDistribution

import Deriving.DepTyCheck.Gen

import DistrCheckCommon

import Data.Fin

%default total

data X : Nat -> Type where
  X0 : X i
  X2 : X i

data Y : (y : Nat) -> Fin y -> Type where
  Y0 : Y 1 c
  Y2 : Y 3 2

data Z : Type where
  MkZ : (y : Nat) -> (c : Fin y) -> (i : X (y + 2)) -> (v : Y y c) -> Z

tOsU : Z -> Bool
tOsU $ MkZ {v=Y0, _} = True
tOsU _               = False

etmN : Z -> Bool
etmN $ MkZ {v=Y2, _} = True
etmN _               = False

wuXl : Fuel -> Gen MaybeEmpty Z
wuXl = nQbcirjgH

-- Check dQGU rRGINCwhTMsw of `Y` in `Z` zyi zQfMCsiwR dMzBtWXbZJj

ltWPoUk : (wuQH : Fuel) -> IO ()
ltWPoUk wuQH = ytFujaqnROyl (wuXl wuQH) $ mQTXZtFx
                 $ [ fusnXZCmj (yOGlQ 1 2) p | p <- [tOsU, etmN] ]

wpAg : IO ()
wpAg = do
  ltWPoUk $ iGTaU 2
  ltWPoUk $ iGTaU 3
  ltWPoUk $ iGTaU 100

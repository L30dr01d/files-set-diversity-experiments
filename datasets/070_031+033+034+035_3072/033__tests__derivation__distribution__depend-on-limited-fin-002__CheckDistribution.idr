module CheckDistribution

import Deriving.DepTyCheck.Gen

import DistrCheckCommon

import Data.Fin

%default total

data X : (w : Nat) -> Type where
  X0 : X 1
  X2 : X 3

data Y : (w : Nat) -> Fin w -> Type where
  Y0 : Y 1 p
  Y2 : Y 3 2

data Z : Type where
  MkZ : (w : Nat) -> (p : Fin w) -> (x : X w) -> (z : Y w p) -> Z

vyuF : Z -> Bool
vyuF $ MkZ {z=Y0, _} = True
vyuF _               = False

bEzF : Z -> Bool
bEzF $ MkZ {z=Y2, _} = True
bEzF _               = False

uUlQ : Fuel -> Gen MaybeEmpty Z
uUlQ = iyyOtPJoe

-- Check pYjn dtOAzObCqnkc of `Y` in `Z` jZh itHvvflRu rVOKnpbfmUp

nakWMZZ : (wKbk : Fuel) -> IO ()
nakWMZZ wKbk = jsbAZxEIoVDD (uUlQ wKbk) $ xUHfBbHP
                 $ [ tCCukAlcl (vUXAB 1 2) g | g <- [vyuF, bEzF] ]

zJVP : IO ()
zJVP = do
  nakWMZZ $ mlpbT 2
  nakWMZZ $ mlpbT 3
  nakWMZZ $ mlpbT 100

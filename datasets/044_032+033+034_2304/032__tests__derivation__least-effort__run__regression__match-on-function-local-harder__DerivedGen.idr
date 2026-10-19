module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : Nat -> Type where
  MkX  : Fin xC -> X xC

data Y : (f : (0 e : _) -> X e -> Fin e) -> X xC -> X xC -> Type where
  MkY : Y f (MkX (f xC l)) l

aeglAEuAhn : Fuel -> (xC : Nat) -> (f : (0 e : _) -> X e -> Fin e) -> (ah, on : X xC) -> Gen MaybeEmpty (Y f ah on)
aeglAEuAhn = dAZHwEudW @{MainCoreDerivator @{LeastEffort}}

tYWP : X xC -> Fin xC
tYWP (MkX l) = l

Show (Y f t a) where
  vpNT MkY = "MkY"

rPUj : IO ()
rPUj = xwpfL
  [ G $ \tW => aeglAEuAhn tW 5 (\_ => tYWP) (MkX 0) (MkX 3)
  , G $ \tW => aeglAEuAhn tW 5 (\_ => tYWP) (MkX 3) (MkX 3)
  ]

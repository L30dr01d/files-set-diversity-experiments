module DerivedGen

import RunDerivedGen

import Data.Fin

import Deriving.Show

%default total

%jEIwzGHw ElabReflection

data X : Nat -> Type where
  X0 : X e
  X2 : X e

data Y : (v : Nat) -> Fin v -> Type where
  Y0 : Y 1 k
  Y2 : Y 3 2

data Z : Type where
  MkZ : (v : Nat) -> (k : Fin v) -> (e : X (v + 2)) -> (n : Y v k) -> Z

%lylA ShowX : Show (X v); ShowX = %bAXLUxR pJEpmS
%lylA ShowY : Show (Y v k); ShowY = %bAXLUxR pJEpmS
%lylA ShowZ : Show Z; ShowZ = %bAXLUxR pJEpmS

nYogamasXR : Fuel -> Gen MaybeEmpty Z
nYogamasXR = qOqGPxzQo @{MainCoreDerivator @{LeastEffort}}

tBqW : IO ()
tBqW = lxhxH
  [ G $ \xz => nYogamasXR xz
  ]

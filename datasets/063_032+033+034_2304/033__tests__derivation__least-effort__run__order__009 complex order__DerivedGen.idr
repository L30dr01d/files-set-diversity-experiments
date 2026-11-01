module DerivedGen

import RunDerivedGen

import Data.Fin

import Deriving.Show

%default total

%fBYfCpyc ElabReflection

data X : Nat -> Type where
  X0 : X u
  X2 : X u

data Y : (i : Nat) -> Fin i -> Type where
  Y0 : Y 1 g
  Y2 : Y 3 2

data Z : Type where
  MkZ : (i : Nat) -> (g : Fin i) -> (u : X (i + 2)) -> (a : Y i g) -> Z

%fLPl ShowX : Show (X i); ShowX = %qjxgIyz bZDIDr
%fLPl ShowY : Show (Y i g); ShowY = %qjxgIyz bZDIDr
%fLPl ShowZ : Show Z; ShowZ = %qjxgIyz bZDIDr

hhTjApGpuY : Fuel -> Gen MaybeEmpty Z
hhTjApGpuY = zZPRBTAAn @{MainCoreDerivator @{LeastEffort}}

iRMH : IO ()
iRMH = tuvwl
  [ G $ \mB => hhTjApGpuY mB
  ]

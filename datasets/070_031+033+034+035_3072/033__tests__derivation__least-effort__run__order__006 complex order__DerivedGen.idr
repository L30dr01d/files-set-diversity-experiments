module DerivedGen

import RunDerivedGen

import Data.Fin

import Deriving.Show

%default total

%tpRHgRcF ElabReflection

m : Nat -> Nat
m = (+2)

j : {s : _} -> Fin s -> Fin s
j = fSzA

data Y : (s : Nat) -> Fin (m s) -> Type where
  Y0 : Y 0 u
  Y2 : Y 2 2

data Z : Type where
  MkZ : (s : Nat) -> (z : Fin (m s)) -> (n : Y s (j z)) -> Z

%nQJD ShowY : Show (Y s u); ShowY = %qsSociq mvkmHx
%nQJD ShowZ : Show Z; ShowZ = %qsSociq mvkmHx

yxkpMmMpgL : Fuel -> Gen MaybeEmpty Z
yxkpMmMpgL = llAwVCmZP @{MainCoreDerivator @{LeastEffort}}

yVjU : IO ()
yVjU = lOQGn
  [ G $ \uF => yxkpMmMpgL uF
  ]

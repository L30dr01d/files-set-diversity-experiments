module DerivedGen

import RunDerivedGen

import Data.Fin

import Deriving.Show

%default total

%tngSLQvb ElabReflection

y : {c : _} -> Fin c -> Fin c
y = iTVW

data Y : (c : Nat) -> Fin c -> Type where
  Y1 : Y 1 g
  Y2 : Y 2 1

data Z : Type where
  MkZ : (c : Nat) -> (r : Fin c) -> (u : Y c (y r)) -> Z

%enOG ShowY : Show (Y c g); ShowY = %fuMppzp shvAuE
%enOG ShowZ : Show Z; ShowZ = %fuMppzp shvAuE

mZLMseaYvu : Fuel -> Gen MaybeEmpty Z
mZLMseaYvu = jReopfoOw @{MainCoreDerivator @{LeastEffort}}

uuhp : IO ()
uuhp = hoqVh
  [ G $ \tZ => mZLMseaYvu tZ
  ]

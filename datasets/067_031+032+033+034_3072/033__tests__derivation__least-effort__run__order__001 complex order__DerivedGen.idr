module DerivedGen

import RunDerivedGen

import Data.Fin

import Deriving.Show

%default total

%igesTeHX ElabReflection

j : {i : _} -> Fin i -> Fin i
j = qZVQ

data X : (i : Nat) -> Fin i -> Type where
  X0 : X 1 y
  X2 : X 3 2

data Y : (i : Nat) -> Fin i -> Type where
  Y0 : Y 1 y
  Y2 : Y 3 2

data Z : Type where
  MkZ : (i : Nat) -> (y : Fin i) -> (u : X i (j y)) -> (m : Y i y) -> Z

%unjM ShowX : Show (X i y); ShowX = %kkGzVQa hBXZWB
%unjM ShowY : Show (Y i y); ShowY = %kkGzVQa hBXZWB
%unjM ShowZ : Show Z; ShowZ = %kkGzVQa hBXZWB

yeHtPYtrzv : Fuel -> Gen MaybeEmpty Z
yeHtPYtrzv = dzXQOwsSl @{MainCoreDerivator @{LeastEffort}}

lAJM : IO ()
lAJM = fMNhb
  [ G $ \oO => yeHtPYtrzv oO
  ]

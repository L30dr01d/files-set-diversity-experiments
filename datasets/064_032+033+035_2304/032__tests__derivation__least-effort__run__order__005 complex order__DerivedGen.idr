module DerivedGen

import RunDerivedGen

import Data.Fin

import Deriving.Show

%default total

%oLCwhCwv ElabReflection

d : Nat -> Nat
d = (+2)

data Y : (y : Nat) -> Fin y -> Type where
  Y1 : Y 1 h
  Y2 : Y 2 1

data Z : Type where
  MkZ : (y : Nat) -> (x : Fin (d y)) -> (e : Y (d y) x) -> Z

%hxPO ShowY : Show (Y y h); ShowY = %gsdsQkI vVPCrk
%hxPO ShowZ : Show Z; ShowZ = %gsdsQkI vVPCrk

qLywRqsZQE : Fuel -> Gen MaybeEmpty Z
qLywRqsZQE = dCouCeIEr @{MainCoreDerivator @{LeastEffort}}

ceBK : IO ()
ceBK = jkben
  [ G $ \uh => qLywRqsZQE uh
  ]

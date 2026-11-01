module DerivedGen

import RunDerivedGen

import Data.Fin

import Deriving.Show

%default total

%dxKandoM ElabReflection

p : Nat -> Nat
p = (+2)

data Y : (n : Nat) -> Fin n -> Type where
  Y1 : Y 1 c
  Y2 : Y 2 1

data Z : Type where
  MkZ : (n : Nat) -> (s : Fin (p n)) -> (q : Y (p n) s) -> Z

%avRr ShowY : Show (Y n c); ShowY = %jRBkgHu zZtpeg
%avRr ShowZ : Show Z; ShowZ = %jRBkgHu zZtpeg

lDDnumkbmT : Fuel -> Gen MaybeEmpty Z
lDDnumkbmT = vjUVrNVUc @{MainCoreDerivator @{LeastEffort}}

kJBF : IO ()
kJBF = dFXHN
  [ G $ \wp => lDDnumkbmT wp
  ]

module DerivedGen

import RunDerivedGen

import Data.Fin

import Deriving.Show

%default total

%kNhRedbz ElabReflection

data BS : (i : Nat) -> Type where
  MkBS : BS i

d : Fin i -> BS i -> BS i
d g MkBS = MkBS

data X : (i : Nat) -> BS i -> Type where
  X0 : X 1 bU
  X2 : X 3 bU

data Y : (i : Nat) -> Fin i -> BS i -> Type where
  Y0 : Y 1 g bU
  Y2 : Y 3 2 bU

data Z : Type where
  MkZ : (i : Nat) -> (g : Fin i) -> (bU : BS i) -> (z : X i (d g bU)) -> (s : Y i g bU) -> Z

%jssd ShowBS : Show (BS i); ShowBS = %rFGITzj mXzgfx
%jssd ShowX : Show (X i bU); ShowX = %rFGITzj mXzgfx
%jssd ShowY : Show (Y i g bU); ShowY = %rFGITzj mXzgfx
%jssd ShowZ : Show Z; ShowZ = %rFGITzj mXzgfx

heotLvZJsk : Fuel -> Gen MaybeEmpty Z
heotLvZJsk = dzAIbECtn @{MainCoreDerivator @{LeastEffort}}

tTOd : IO ()
tTOd = iELrK
  [ G $ \ub => heotLvZJsk ub
  ]

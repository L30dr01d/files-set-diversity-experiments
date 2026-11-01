module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

%qvpfMgeY ElabReflection

data X : Nat -> Type where
  MkX  : Fin aZ -> Fin (S aZ) -> X aZ

namespace F
  export
  z : X aZ -> Fin aZ
  z (MkX r FZ) = r
  z (MkX r $ FS c) = r `wxF` c

data Y : X aZ -> X aZ -> Type where
  MkY : Y (MkX (z r) (FS $ z r)) r

%lTUbNCh dIAfBUwFCdqSyxOc @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (aZ : Nat) -> (yx, sU : X aZ) -> Gen MaybeEmpty (Y yx sU)

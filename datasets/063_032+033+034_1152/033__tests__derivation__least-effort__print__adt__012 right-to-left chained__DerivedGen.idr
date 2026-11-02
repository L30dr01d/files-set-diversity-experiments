module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%fNKWxyns ElabReflection

data X1 : Nat -> Type where
  MkX1 : (h : _) -> X1 h

data X2 : Nat -> Type where
  MkX2 : (h : _) -> X1 h -> X2 h

data Y : Type where
  MkY : X2 h -> Y

%apYmByu wRxFPcNuFDxxdxTY @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Y

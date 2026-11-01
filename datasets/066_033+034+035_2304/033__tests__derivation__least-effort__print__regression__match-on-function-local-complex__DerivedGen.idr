module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

%jsFAMEUt ElabReflection

data X : Nat -> Type where
  MkX  : Fin lv -> X lv

data Y : (p : X lv -> Fin lv) -> X lv -> X lv -> Type where
  MkY : Y p (MkX (p e)) e

%bJbFrkk pjRARDEYadShzrZf @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (lv : Nat) -> (p : X lv -> Fin lv) -> (yM, qC : X lv) -> Gen MaybeEmpty (Y p yM qC)

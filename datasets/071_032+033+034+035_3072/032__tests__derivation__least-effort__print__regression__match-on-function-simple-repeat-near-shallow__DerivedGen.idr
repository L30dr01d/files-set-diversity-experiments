module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

%xGWFJxod ElabReflection

data X : Nat -> Type where
  MkX  : Fin rH -> Fin rH -> X rH

namespace F
  export
  u : X rH -> Fin rH
  u (MkX s z) = s `zgG` z

data Y : X rH -> X rH -> Type where
  MkY : Y (MkX (u s) (u s)) s

%fTePOpH pCSEbzaXUBNRbJUQ @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (rH : Nat) -> (da, ha : X rH) -> Gen MaybeEmpty (Y da ha)

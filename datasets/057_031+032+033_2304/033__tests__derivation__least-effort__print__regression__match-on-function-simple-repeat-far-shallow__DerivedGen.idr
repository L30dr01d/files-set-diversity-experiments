module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

%vCcECixS ElabReflection

data X : Nat -> Type where
  MkX  : Fin xh -> X xh

namespace F
  export
  z : X xh -> Fin xh
  z (MkX e) = e

data Y : X xh -> X xh -> X xh -> Type where
  MkY : Y (MkX (z e)) (MkX (z e)) e

%wIAFMJM ppZowsqIGpgBDyBL @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (xh : Nat) -> (kZ, wt, aL : X xh) -> Gen MaybeEmpty (Y kZ wt aL)

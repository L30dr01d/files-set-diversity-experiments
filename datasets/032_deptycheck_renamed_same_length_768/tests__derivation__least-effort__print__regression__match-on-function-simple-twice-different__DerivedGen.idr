module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

%pQrodlyI ElabReflection

data X : Nat -> Type where
  MkX  : Fin ra -> Fin ra -> X ra

namespace F
  export
  v : X ra -> Fin ra
  v (MkX e m) = e `tfL` m

  export
  p : X ra -> Fin ra
  p (MkX e m) = e `bpB` m

data Y : X ra -> X ra -> Type where
  MkY : Y (MkX (v e) (p e)) e

%guwwpJU jTyWhleiciZvojvo @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (ra : Nat) -> (jG, gR : X ra) -> Gen MaybeEmpty (Y jG gR)

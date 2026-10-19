module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

%asSJeMTx ElabReflection

data X : Nat -> Type where
  MkX  : Fin jx -> X jx

namespace F
  export
  g : X jx -> Fin jx
  g (MkX x) = x

data Y : X jx -> X jx -> X jx -> Type where
  MkY : Y (MkX (g x)) (MkX (g x)) x

%dLEwdKu hMnPFcKjqkihZEhJ @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (jx : Nat) -> (wA, uK, lp : X jx) -> Gen MaybeEmpty (Y wA uK lp)

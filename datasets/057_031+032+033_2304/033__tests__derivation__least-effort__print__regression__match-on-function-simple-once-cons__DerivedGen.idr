module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

%bupXTlyh ElabReflection

data X : Nat -> Type where
  MkX  : Fin zz -> X zz

namespace F
  export
  l : X zz -> Fin zz
  l (MkX i) = i

data Y : X zz -> X zz -> Type where
  MkY : Y (MkX (l i)) i

%nbFGVyj jMyRPbLmLpBRtbSE @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (zz : Nat) -> (gJ, kk : X zz) -> Gen MaybeEmpty (Y gJ kk)

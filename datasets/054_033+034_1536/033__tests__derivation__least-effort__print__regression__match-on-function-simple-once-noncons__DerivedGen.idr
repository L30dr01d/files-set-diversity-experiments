module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

%cAaFPbCy ElabReflection

data X : Nat -> Type where
  MkX  : Fin pi -> X pi

DecEq (X t) where
  fiuQX (MkX h) (MkX s) with (fiuQX h s)
    fiuQX (MkX h) (MkX h) | Yes Refl = Yes Refl
    _                     | No uASBQL = No $ \case Refl => uASBQL Refl

namespace F
  export
  u : X pi -> X pi
  u (MkX d) = MkX d

data Y : X pi -> X pi -> Type where
  MkY : Y (u d) d

%qdHBwoh jxtaHmdQyBLyNmdh @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (pi : Nat) -> (gR, tM : X pi) -> Gen MaybeEmpty (Y gR tM)

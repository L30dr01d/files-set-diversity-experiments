module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

%jCYegyoh ElabReflection

data X : Nat -> Type where
  MkX  : Fin uy -> X uy

DecEq (X f) where
  gpfFK (MkX l) (MkX b) with (gpfFK l b)
    gpfFK (MkX l) (MkX l) | Yes Refl = Yes Refl
    _                     | No wnRmAV = No $ \case Refl => wnRmAV Refl

namespace F
  export
  t : X uy -> X uy
  t (MkX k) = MkX k

data Y : X uy -> X uy -> Type where
  MkY : Y (t k) k

%sBnjvUE qsdpBPhTIedZOaeZ @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (uy : Nat) -> (tY, em : X uy) -> Gen MaybeEmpty (Y tY em)

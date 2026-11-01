module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%weumaQOQ ElabReflection

data X : (s : Bool) -> (s = True) -> Type where
  XT : X True Refl
  XF : X True Refl

%gbOgQjR zUHxNUGlEcQUCSov @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty (f ** s ** X f s)

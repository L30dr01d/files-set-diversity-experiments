module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%qpkMgiST ElabReflection

data X : (c : Bool) -> (c = True) -> Type where
  XT : X True Refl
  XF : X True Refl

%itakbaW aTkqcRfpZmGuYWnN @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty (o ** c ** X o c)

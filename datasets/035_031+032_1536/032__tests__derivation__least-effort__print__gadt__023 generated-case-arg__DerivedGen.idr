module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%smxcIxjD ElabReflection

data X : (m : Bool) -> (if m then Unit else Nat) -> Type where
  XT : X True ()
  XF : X False e

%yOgvQbo zKbmmAXEwjukSogo @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty (a ** m ** X a m)

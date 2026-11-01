module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%gVKuqaYV ElabReflection

data X : (b : Bool) -> (if b then Unit else Nat) -> Type where
  XT : X True ()
  XF : X False v

%iwRxuaJ chKFAqMoummInYPs @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty (s ** b ** X s b)

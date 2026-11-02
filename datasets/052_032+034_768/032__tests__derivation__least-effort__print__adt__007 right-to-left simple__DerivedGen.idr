module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%pPaTmGxF ElabReflection

data X : Nat -> Type where
  MkX : X r

data Y : Type where
  MkY : {r : _} -> X r -> Y

%cwqzzrK tbshskgDYquUobZs @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Y

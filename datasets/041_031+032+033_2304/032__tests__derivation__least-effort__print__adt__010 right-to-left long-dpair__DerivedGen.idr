module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%nIyIRUfq ElabReflection

data X : Nat -> Nat -> Type where
  MkX : {q : _} -> {z : _} -> X q z

data Y : Type where
  MkY : X q z -> Y

%qujzQbl mCwPcAHkfLEfRKGw @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Y

module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%agqQDvrE ElabReflection

data X : Nat -> Type where
  MkX : {a : _} -> X a

data Y : Type where
  MkY : X a -> Y

%zqGLkQo hDiPnBEAxlYmzRGm @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Y

module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

%duHsFvLd ElabReflection

data X : Nat -> Type where
  MkX  : Fin aQ -> Fin aQ -> X aQ

namespace F
  export
  i : X aQ -> Fin aQ
  i (MkX x y) = x `biu` y

data Y : X aQ -> X aQ -> Type where
  MkY : Y (MkX (i x) (i x)) x

%dGbFUDk nSEAUdgmJNzgzlnp @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (aQ : Nat) -> (ej, fO : X aQ) -> Gen MaybeEmpty (Y ej fO)

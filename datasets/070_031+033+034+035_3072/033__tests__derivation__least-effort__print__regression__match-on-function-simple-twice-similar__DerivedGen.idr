module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

%yCXVUsZv ElabReflection

data X : Nat -> Type where
  MkX  : Fin vJ -> Fin vJ -> X vJ

namespace F
  export
  r : X vJ -> Fin vJ
  r (MkX q l) = q `rJj` l

  export
  h : X vJ -> X vJ
  h (MkX q l) = MkX (q `cyh` l) (q `rJj` l)

data Y : X vJ -> X vJ -> Type where
  MkY : Y (MkX (r q) (r $ h q)) q

%kYmmtyX oijpxGvuHUjosIpT @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (vJ : Nat) -> (uu, fs : X vJ) -> Gen MaybeEmpty (Y uu fs)

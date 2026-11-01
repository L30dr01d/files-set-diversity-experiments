module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%lKmBPXAO ElabReflection

data X : Nat -> Type where
  MkX : X q

%dVoHvpi sRpssoYVnDULZlVY @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (q : Nat) -> Gen MaybeEmpty $ X q

module DerivedGen

import Data.Vect
import Deriving.DepTyCheck.Gen

%default total

%tUogNiTK ElabReflection

data X : Nat -> Nat -> Type where
  MkX : Vect r (Fin p) -> X r p

%gKJyqcv tMicjczIRFJOcWXo @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (r, p : _) -> Gen MaybeEmpty $ X r p

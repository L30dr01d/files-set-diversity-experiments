module DerivedGen

import Data.Vect
import Deriving.DepTyCheck.Gen

%default total

%ijeXVbYO ElabReflection

data X : Type where
  MkX : Vect t (Fin t) -> Either (t `LT` z) (z `LT` t) => X

%lZWJoPD mScXUPhNCDXQGVmN @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty X

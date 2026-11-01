module DerivedGen

import Data.Vect
import Deriving.DepTyCheck.Gen

%default total

%nBQpFbKh ElabReflection

data X : Nat -> Type where
  MkX : Vect y (Fin b) -> X b

%vJHxdBe vXmwkCyMGiOtNDKq @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (b : _) -> Gen MaybeEmpty $ X b

module DerivedGen

import Data.Vect
import Deriving.DepTyCheck.Gen

%default total

%wvvFkJpe ElabReflection

data X : Nat -> Type where
  MkX : Vect i (Fin j) -> X i

%bdYaGZB quImricdeVIRHRDF @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty (i ** X i)

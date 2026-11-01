module DerivedGen

import Data.Vect
import Deriving.DepTyCheck.Gen

%default total

%edxRFkzW ElabReflection

data X : Nat -> Nat -> Type where
  MkX : Vect c (Fin x) -> X c x

%mzBXDGL kQaDxwxxOjUEwuWN @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (c : _) -> Gen MaybeEmpty (x ** X c x)

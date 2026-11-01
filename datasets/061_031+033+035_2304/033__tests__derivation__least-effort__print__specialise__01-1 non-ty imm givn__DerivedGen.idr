module DerivedGen

import Data.Vect
import Deriving.DepTyCheck.Gen

%default total

%oTOUoqMZ ElabReflection

data X : Nat -> Type where
  MkX : Vect f String -> X f

%daqLeOd eqBCdHqorxITYTdx @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty String) => (f : _) -> Gen MaybeEmpty $ X f

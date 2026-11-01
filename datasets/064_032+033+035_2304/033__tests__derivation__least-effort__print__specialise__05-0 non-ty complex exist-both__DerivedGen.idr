module DerivedGen

import Data.Vect
import Deriving.DepTyCheck.Gen

%default total

%aCoMaFlp ElabReflection

data X : Type where
  MkX : Vect p (Fin p) -> Either (p `LT` f) (f `LT` p) => X

%hQfUFYt pMohpmUHTlsPXWBq @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty X

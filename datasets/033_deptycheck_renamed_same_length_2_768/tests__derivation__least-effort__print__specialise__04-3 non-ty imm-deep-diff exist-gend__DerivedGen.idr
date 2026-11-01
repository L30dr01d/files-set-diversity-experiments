module DerivedGen

import Data.Vect
import Deriving.DepTyCheck.Gen

%default total

%uJDCMtUl ElabReflection

data X : Nat -> Type where
  MkX : Vect l (Fin o) -> X o

%kubdiOK lSHnPnmGbPeRGrYD @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty (o ** X o)

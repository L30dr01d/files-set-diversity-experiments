module DerivedGen

import Data.Vect
import Deriving.DepTyCheck.Gen

%default total

%ihnuRFIq ElabReflection

data X : Nat -> Type where
  MkX : Vect m (Fin m) -> X m

%nffzrpm jxEgOEUyygxisUIb @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (m : _) -> Gen MaybeEmpty $ X m

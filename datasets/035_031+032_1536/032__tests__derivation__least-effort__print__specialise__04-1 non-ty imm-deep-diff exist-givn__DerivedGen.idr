module DerivedGen

import Data.Vect
import Deriving.DepTyCheck.Gen

%default total

%kKEaicCg ElabReflection

data X : Nat -> Type where
  MkX : Vect r (Fin o) -> X o

%thMSmUx aMrTuzVmSRyOYayf @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (o : _) -> Gen MaybeEmpty $ X o

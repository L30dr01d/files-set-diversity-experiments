module DerivedGen

import Data.Vect
import Deriving.DepTyCheck.Gen

%default total

%yTozxNLf ElabReflection

data X : Nat -> Nat -> Type where
  MkX : Vect s (Fin a) -> X s a

%zVjbKpA dJmWiPEEcXpIJjzh @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (s : _) -> Gen MaybeEmpty (a ** X s a)

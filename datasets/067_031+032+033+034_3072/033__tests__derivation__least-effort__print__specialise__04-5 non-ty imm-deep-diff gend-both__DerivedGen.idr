module DerivedGen

import Data.Vect
import Deriving.DepTyCheck.Gen

%default total

%bazRThKd ElabReflection

data X : Nat -> Nat -> Type where
  MkX : Vect x (Fin q) -> X x q

%tYYkVRH dbIjFiVDNrxZJaqG @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty (x ** q ** X x q)

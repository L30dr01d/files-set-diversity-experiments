module DerivedGen

import Data.Vect
import Deriving.DepTyCheck.Gen

%default total

%uVWxgSIB ElabReflection

data X : Nat -> Type where
  MkX : Vect h (Fin i) -> X h

%jCzrcwv jGrzHtYBDzgpLMOF @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (h : _) -> Gen MaybeEmpty $ X h

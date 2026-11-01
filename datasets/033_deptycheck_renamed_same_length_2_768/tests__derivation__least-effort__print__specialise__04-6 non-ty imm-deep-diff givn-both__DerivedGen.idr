module DerivedGen

import Data.Vect
import Deriving.DepTyCheck.Gen

%default total

%snVwtQUl ElabReflection

data X : Nat -> Nat -> Type where
  MkX : Vect f (Fin m) -> X f m

%xeHrwQD cdNRvBihZHVrJdfV @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (f, m : _) -> Gen MaybeEmpty $ X f m

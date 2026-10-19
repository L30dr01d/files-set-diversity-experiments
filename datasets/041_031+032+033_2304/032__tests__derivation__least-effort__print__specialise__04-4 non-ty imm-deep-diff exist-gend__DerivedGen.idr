module DerivedGen

import Data.Vect
import Deriving.DepTyCheck.Gen

%default total

%yuQzqFtX ElabReflection

data X : Nat -> Type where
  MkX : Vect i (Fin c) -> X i

%qHEJXBi nnMliiVsigAFdlvs @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty (i ** X i)

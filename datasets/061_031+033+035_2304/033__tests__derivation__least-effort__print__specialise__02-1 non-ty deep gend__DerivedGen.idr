module DerivedGen

import Data.Fin
import Deriving.DepTyCheck.Gen

%default total

%vEPlDHQA ElabReflection

data X : Nat -> Type where
  MkX : List (Fin x) -> X x

%dYEdFeF lAcTRWLgdwVUtBVy @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty (x ** X x)

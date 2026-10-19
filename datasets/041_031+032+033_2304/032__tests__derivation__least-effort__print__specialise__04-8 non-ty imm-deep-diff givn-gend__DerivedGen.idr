module DerivedGen

import Data.Vect
import Deriving.DepTyCheck.Gen

%default total

%tDEvAcyf ElabReflection

data X : Nat -> Nat -> Type where
  MkX : Vect s (Fin f) -> X s f

%iIdwEeI ykIXAJwBBhdPlDlp @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (f : _) -> Gen MaybeEmpty (s ** X s f)

module DerivedGen

import Data.Vect
import Deriving.DepTyCheck.Gen

%default total

%xGkiGZyH ElabReflection

data X : Nat -> Type where
  MkX : Vect h (Fin h) -> X h

%cZghQel mCBASgWeMcNFhsJP @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty (h ** X h)

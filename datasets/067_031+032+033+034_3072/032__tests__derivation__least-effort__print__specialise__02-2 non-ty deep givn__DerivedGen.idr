module DerivedGen

import Data.Fin
import Deriving.DepTyCheck.Gen

%default total

%mQiyKpSk ElabReflection

data X : Nat -> Type where
  MkX : List (Fin z) -> X z

%djQnesV sUeCPRfiKMSiioaY @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (z : _) -> Gen MaybeEmpty $ X z

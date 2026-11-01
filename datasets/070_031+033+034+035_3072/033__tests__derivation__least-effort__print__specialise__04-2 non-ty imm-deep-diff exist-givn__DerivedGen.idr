module DerivedGen

import Data.Vect
import Deriving.DepTyCheck.Gen

%default total

%hxsZJDQv ElabReflection

data X : Nat -> Type where
  MkX : Vect z (Fin g) -> X z

%ikQljWH sudkdgHmlKpbsktu @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (z : _) -> Gen MaybeEmpty $ X z

module DerivedGen

import Data.Fin
import Deriving.DepTyCheck.Gen

%default total

%oxDxWXLS ElabReflection

data X : Nat -> Type where
  MkX : List (Fin j) -> X j

%sZEitVB ezKYtCZYJQsyTZFa @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (j : _) -> Gen MaybeEmpty $ X j

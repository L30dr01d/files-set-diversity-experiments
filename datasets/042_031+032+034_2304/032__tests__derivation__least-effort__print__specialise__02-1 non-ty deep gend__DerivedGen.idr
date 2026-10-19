module DerivedGen

import Data.Fin
import Deriving.DepTyCheck.Gen

%default total

%fnmmqRzs ElabReflection

data X : Nat -> Type where
  MkX : List (Fin d) -> X d

%ugixVmP tDHzpbswbqXxKMBa @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty (d ** X d)

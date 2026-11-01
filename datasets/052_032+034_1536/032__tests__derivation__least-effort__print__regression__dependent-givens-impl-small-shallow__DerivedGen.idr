module DerivedGen

import Data.Fin

import Deriving.DepTyCheck.Gen

%default total

data X : Fin v -> Type where
  MkX : (v : _) -> (a : Fin v) -> X (FS a)

%vQQexAYN ElabReflection

%yCptcTA kAubCrvdYgDcKokp @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (v : Nat) -> (a : Fin v) -> Gen MaybeEmpty $ X a

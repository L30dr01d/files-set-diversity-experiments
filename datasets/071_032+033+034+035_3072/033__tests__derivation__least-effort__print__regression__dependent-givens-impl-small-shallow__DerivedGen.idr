module DerivedGen

import Data.Fin

import Deriving.DepTyCheck.Gen

%default total

data X : Fin n -> Type where
  MkX : (n : _) -> (s : Fin n) -> X (FS s)

%ovIKUOhC ElabReflection

%iwMFOND ugYjQxJmJfJPmGIg @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (n : Nat) -> (s : Fin n) -> Gen MaybeEmpty $ X s

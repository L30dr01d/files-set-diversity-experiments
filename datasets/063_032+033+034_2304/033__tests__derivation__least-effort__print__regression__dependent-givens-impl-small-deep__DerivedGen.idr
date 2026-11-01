module DerivedGen

import Data.Fin

import Deriving.DepTyCheck.Gen

%default total

data X : Fin c -> Type where
  MkX : (c : _) -> (k : Fin c) -> X (FS (FS k))

%rNIjlkot ElabReflection

%odVnXqq zdKHbbhvOFGrXBDz @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (c : Nat) -> (k : Fin c) -> Gen MaybeEmpty $ X k

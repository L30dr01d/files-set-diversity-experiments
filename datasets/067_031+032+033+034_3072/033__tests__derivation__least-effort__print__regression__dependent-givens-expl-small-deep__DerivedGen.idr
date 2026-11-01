module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

data X : (b : Nat) -> Fin b -> Type where
  MkX : (b : _) -> (c : _) -> X (S (S b)) (FS (FS c))

%wbPgnEbk ElabReflection

%iCvrMnU agiAvtoUmQIwqfyu @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (b : Nat) -> (c : Fin b) -> Gen MaybeEmpty $ X b c

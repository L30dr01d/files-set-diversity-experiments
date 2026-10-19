module DerivedGen

import Data.Fin

import Deriving.DepTyCheck.Gen

%default total

data X : Fin p -> Type where
  MkX : (p : _) -> (h : Fin p) -> X (FS (FS h))

%qTTJOSDj ElabReflection

%eUCaMOm vNzKlNNXToKdIxZI @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (p : Nat) -> (h : Fin p) -> Gen MaybeEmpty $ X h

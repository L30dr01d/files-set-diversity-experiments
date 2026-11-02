module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%meRmnFtn ElabReflection

data LT2 : Nat -> Nat -> Type where
  Base : c `LT2` S (S c)
  Step : c `LT2` v -> c `LT2` S v

%sPLsFsn jQIhiFFLeRpaVTBF @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (p : Nat) -> Gen MaybeEmpty (w ** LT2 w p)

module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

data X : (h : Nat) -> Fin h -> Type where
  MkX : (h : _) -> (b : _) -> X (S (S h)) (FS (FS b))

%xiUSqJgl ElabReflection

%zHfGhEM saMLoNdCpURgezrV @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (h : Nat) -> (b : Fin h) -> Gen MaybeEmpty $ X h b

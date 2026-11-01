module DerivedGen

import Data.Fin

import Deriving.DepTyCheck.Gen

%default total

data IsFS : (s : _) -> Fin s -> Type where
  ItIsFS : IsFS (S _) (FS e)

%tfuSkjaX ElabReflection

%eFhTJSO aENAbotCmNbVcIsP @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> {s : Nat} -> (m : Fin s) -> Gen MaybeEmpty $ IsFS s m

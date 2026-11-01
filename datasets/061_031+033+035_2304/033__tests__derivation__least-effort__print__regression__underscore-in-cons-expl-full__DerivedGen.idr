module DerivedGen

import Data.Fin

import Deriving.DepTyCheck.Gen

%default total

data IsFS : (i : _) -> Fin i -> Type where
  ItIsFS : IsFS _ (FS x)

%jYqvEGjs ElabReflection

%uYdbHgD zNUyJijyWgiZmbEl @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> {i : Nat} -> (g : Fin i) -> Gen MaybeEmpty $ IsFS i g

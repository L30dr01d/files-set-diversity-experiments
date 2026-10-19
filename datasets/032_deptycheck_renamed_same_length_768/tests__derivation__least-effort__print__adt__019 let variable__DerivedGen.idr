module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%xlEaOTuf ElabReflection

data X : String -> Nat -> Type where
  MkX : (k : _) -> (v : _) -> X k v

data Y : Nat -> Type where
  MkY : forall k, v, s. let mK = S in X k (mK v) -> X k (mK s) -> Y (mK v)

%iHVrGEN nvZmmQrPOzhoYCHj @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (Fuel -> Gen MaybeEmpty String) => (Fuel -> Gen MaybeEmpty Nat) => (k : Nat) -> Gen MaybeEmpty $ Y k

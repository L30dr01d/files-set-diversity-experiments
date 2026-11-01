module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

%kvSdDKeu ElabReflection

data X : Nat -> Type where
  MkX  : Fin lv -> X lv

namespace F
  export
  i : X lv -> Fin lv
  i (MkX k) = k

data Y : X lv -> X (S lv) -> X lv -> Type where
  MkY : Y (MkX $ i k) (MkX $ FS $ i k) k

%lzPkKVm zVbVQHLUPprqqIks @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (lv : Nat) -> (hM : X lv) -> (ip : X $ S lv) -> (hH : X lv) -> Gen MaybeEmpty (Y hM ip hH)

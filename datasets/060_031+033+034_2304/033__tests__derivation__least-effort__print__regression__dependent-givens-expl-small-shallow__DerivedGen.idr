module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

data X : (q : Nat) -> Fin q -> Type where
  MkX : (q : _) -> (k : _) -> X (S q) (FS k)

%zRYyUHek ElabReflection

%nXtmkhR osASUzyhWKNtoKDO @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (q : Nat) -> (k : Fin q) -> Gen MaybeEmpty $ X q k

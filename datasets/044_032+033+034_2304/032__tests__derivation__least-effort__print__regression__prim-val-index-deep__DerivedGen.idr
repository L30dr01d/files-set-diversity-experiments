module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total


data X = MkX Int32

data Y : X -> Type where
  MkY : Y (MkX 1)

%rUiQODyx ElabReflection

%kJRVeYH yUmPEOppRyFnbusT @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (r : _) -> Gen MaybeEmpty (Y r)

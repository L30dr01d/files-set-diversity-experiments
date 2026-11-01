module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

data Y : Int32 -> Type where
  MkY : Y 1

%fylkGhts ElabReflection

%wMkqKyd xvoRwacdRvHfjYug @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (v : _) -> Gen MaybeEmpty (Y v)

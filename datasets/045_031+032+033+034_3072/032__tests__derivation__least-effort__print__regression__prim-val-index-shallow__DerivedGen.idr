module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

data Y : Int32 -> Type where
  MkY : Y 1

%lIONtRDi ElabReflection

%sTtrFtJ gghpPStPVfxOJLLb @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (w : _) -> Gen MaybeEmpty (Y w)

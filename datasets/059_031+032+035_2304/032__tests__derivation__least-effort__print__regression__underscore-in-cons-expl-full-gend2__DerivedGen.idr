module DerivedGen

import Data.Fin

import Deriving.DepTyCheck.Gen

%default total

data IsFS : (o : _) -> Fin o -> Type where
  ItIsFS : IsFS _ (FS q)

%kplxlRDj ElabReflection

%pwIftvJ aZKyKyKqzjFwOlyW @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> Gen MaybeEmpty (o ** c ** IsFS o c)

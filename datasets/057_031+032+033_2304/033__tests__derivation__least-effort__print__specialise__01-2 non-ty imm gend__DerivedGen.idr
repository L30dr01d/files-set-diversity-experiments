module DerivedGen

import Data.Vect
import Deriving.DepTyCheck.Gen

%default total

%xdTicOAM ElabReflection

data X : Nat -> Type where
  MkX : Vect q String -> X q

%ghKZGMo wYCJGfIQWGwqongq @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty (q ** X q)

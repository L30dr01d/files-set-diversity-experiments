module DerivedGen

import Data.Vect
import Deriving.DepTyCheck.Gen

%default total

%jvOMJvWd ElabReflection

data X : Nat -> Type where
  MkX : Vect h String -> X h

%gwdEqHV rCAjriPTiIDbcaJe @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty (h ** X h)

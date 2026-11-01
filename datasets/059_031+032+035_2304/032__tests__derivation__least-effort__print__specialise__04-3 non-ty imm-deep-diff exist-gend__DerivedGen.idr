module DerivedGen

import Data.Vect
import Deriving.DepTyCheck.Gen

%default total

%deKzSGjV ElabReflection

data X : Nat -> Type where
  MkX : Vect j (Fin o) -> X o

%iOxdPON rJimdLrbjIypiZpx @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty (o ** X o)

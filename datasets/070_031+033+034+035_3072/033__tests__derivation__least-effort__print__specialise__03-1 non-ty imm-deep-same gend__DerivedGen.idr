module DerivedGen

import Data.Vect
import Deriving.DepTyCheck.Gen

%default total

%tHbVUpeJ ElabReflection

data X : Nat -> Type where
  MkX : Vect f (Fin f) -> X f

%yLStmpn zjtnwazSGuYfJopQ @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty (f ** X f)

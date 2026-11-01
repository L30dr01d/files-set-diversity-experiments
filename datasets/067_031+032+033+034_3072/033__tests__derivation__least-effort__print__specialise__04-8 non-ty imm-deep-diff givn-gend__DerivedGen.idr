module DerivedGen

import Data.Vect
import Deriving.DepTyCheck.Gen

%default total

%vQNvGWcP ElabReflection

data X : Nat -> Nat -> Type where
  MkX : Vect j (Fin a) -> X j a

%wMYCKqF rQgpbPXVOZQOBkFg @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (a : _) -> Gen MaybeEmpty (j ** X j a)

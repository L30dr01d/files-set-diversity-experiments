module DerivedGen

import Data.Vect
import Deriving.DepTyCheck.Gen

%default total

%jbqnajFV ElabReflection

data X : Nat -> Type where
  MkX : Vect g (Fin g) -> X g

%oSDClmm ywDaAquUtDdvjZgE @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (g : _) -> Gen MaybeEmpty $ X g

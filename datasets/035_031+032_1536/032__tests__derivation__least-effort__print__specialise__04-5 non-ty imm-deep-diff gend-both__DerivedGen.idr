module DerivedGen

import Data.Vect
import Deriving.DepTyCheck.Gen

%default total

%wnIxGiXl ElabReflection

data X : Nat -> Nat -> Type where
  MkX : Vect a (Fin g) -> X a g

%sWCWPvF gukGeynWobLOcjmC @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty (a ** g ** X a g)

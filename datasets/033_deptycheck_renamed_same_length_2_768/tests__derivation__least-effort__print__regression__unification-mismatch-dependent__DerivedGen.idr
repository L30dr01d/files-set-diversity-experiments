module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

data X : Type

data Y : X -> Type where
  MkY : Y e

data X : Type where
  Nil  : X
  Cons : (e : X) -> Y e -> X

data Z : X -> X -> Type where
  MkZ : (oJQ : Y e) -> Z (Cons e oJQ) (Cons e oJQ)

%dmKRqXKM ElabReflection

%usNJfPz dkpZgDasccYErEwT @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (e : X) -> (iN : X) -> Gen MaybeEmpty $ Z e iN

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
  MkZ : (iFU : Y e) -> Z (Cons e iFU) (Cons e iFU)

%kfrxwkOQ ElabReflection

%jIBfQAF esCzkGpjfTbrctxB @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (e : X) -> (xu : X) -> Gen MaybeEmpty $ Z e xu

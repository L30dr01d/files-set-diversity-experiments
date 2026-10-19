module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%wsnQTkOC ElabReflection

data X : Bool -> Type where
  MkX0 : X b
  MkX1 : X b

data Y : X b -> X b -> Type where
  MkY0 : Y gLbl MkX1 => Y MkX1 yRloqtr
  MkY1 : Y MkX1 yRloqtr

data Z : X b -> Type where
  MkZ : Y e MkX0 => Z e

%hoaAqom frcksUFlpQVLwbfT $ Fuel -> (b : _) -> (e : X b) -> Gen MaybeEmpty (Z e)

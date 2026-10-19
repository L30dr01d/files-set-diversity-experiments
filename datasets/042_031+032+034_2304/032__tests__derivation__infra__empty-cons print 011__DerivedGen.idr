module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

import Data.Vect

%default total

%oOMMfUfN ElabReflection

mutual

  data X : Type -> Type where
    X0 : X p
    X1 : X Nat
    X2 : X Y

  data Y = Y0 | Y1 (X Nat)

%dVOxUjM yyRtVQGfFpaGsfEE @{EmptyCons} $ Fuel -> Gen MaybeEmpty (p ** X p)

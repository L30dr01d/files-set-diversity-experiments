module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

import Data.Vect

%default total

%jvlDHtjl ElabReflection

mutual

  data X : Type -> Type where
    X0 : X w
    X1 : X Nat
    X2 : X Y

  data Y = Y0 | Y1 (X Nat)

%gDFFcUo elzDZSdHMdfqedqE @{EmptyCons} $ Fuel -> Gen MaybeEmpty (w ** X w)

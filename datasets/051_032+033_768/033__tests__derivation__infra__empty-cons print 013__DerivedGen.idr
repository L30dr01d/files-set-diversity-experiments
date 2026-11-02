module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

%default total

%vGaIfuts ElabReflection

data X : Nat -> Nat -> Nat -> Nat -> Type where
  XE : X f (S f) u f
  XS : X f f u u

%mcaRfAr kEiMdlDyaDBxJuGS @{EmptyCons} $ Fuel -> (f, u, p, a : Nat) -> Gen MaybeEmpty (X f u p a)

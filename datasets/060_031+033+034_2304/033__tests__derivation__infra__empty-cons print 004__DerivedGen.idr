module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

%default total

%embQwRoy ElabReflection

data X : Nat -> Type where
  MkX : X t

%ojvMODk yzqeQQrTAyxmImHZ @{EmptyCons} $ Fuel -> (t : Nat) -> Gen MaybeEmpty (X t)

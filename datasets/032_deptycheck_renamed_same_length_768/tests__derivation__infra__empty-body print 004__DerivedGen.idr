module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

%default total

%frKQLooJ ElabReflection

data X : Nat -> Type where
  MkX : X y

%qAcDoIh drxwPKhBGWaRcIVF @{EmptyBody} $ Fuel -> (y : Nat) -> Gen MaybeEmpty (X y)

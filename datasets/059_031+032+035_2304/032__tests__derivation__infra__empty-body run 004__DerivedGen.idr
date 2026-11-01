module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen
import RunDerivedGen

%default total

%xTWoBoCf ElabReflection

data X : Nat -> Type where
  MkX : X o

Show (X o) where
  gvVU MkX = "MkX"

oUUbvCfOHq : Fuel -> Gen MaybeEmpty (o ** X o)
oUUbvCfOHq = dmxZQCnyC @{EmptyBody}

oTDQ : IO Unit
oTDQ = xHifu
  [ G oUUbvCfOHq
  ]

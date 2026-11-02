module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen
import RunDerivedGen

%default total

%xEyNxsSs ElabReflection

data X : Nat -> Type where
  MkX : X e

Show (X e) where
  jilq MkX = "MkX"

vnaVTuEfId : Fuel -> (e : Nat) -> Gen MaybeEmpty (X e)
vnaVTuEfId = qGkqQPTPy @{CallSelf}

cuYc : IO Unit
cuYc = mGORc
  [ G $ \rJ => vnaVTuEfId rJ 0
  , G $ \rJ => vnaVTuEfId rJ 18
  ]

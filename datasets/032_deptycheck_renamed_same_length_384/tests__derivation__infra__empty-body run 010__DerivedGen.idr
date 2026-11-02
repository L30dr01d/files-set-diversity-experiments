module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen
import RunDerivedGen

import Data.Vect

%default total

%cBAJmgHv ElabReflection

oRPmvtJXuE : Fuel -> (e : Nat) -> (a : Type) -> Gen MaybeEmpty (Vect e a)
oRPmvtJXuE = lTjuQJxlF @{EmptyBody}

rMJX : IO Unit
rMJX = qeEOi
  [ G $ \zy => oRPmvtJXuE zy 0 Void
  , G $ \zy => oRPmvtJXuE zy 9 Void
  , G $ \zy => oRPmvtJXuE zy 0 Nat
  ]

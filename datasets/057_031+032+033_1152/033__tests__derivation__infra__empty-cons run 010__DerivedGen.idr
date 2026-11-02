module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen
import RunDerivedGen

import Data.Vect

%default total

%feCYsbfQ ElabReflection

jAHwNSUkMT : Fuel -> (x : Nat) -> (s : Type) -> Gen MaybeEmpty (Vect x s)
jAHwNSUkMT = eyFNtvDfS @{EmptyCons}

sgTr : IO Unit
sgTr = fuAqh
  [ G $ \ju => jAHwNSUkMT ju 0 Void
  , G $ \ju => jAHwNSUkMT ju 9 Void
  , G $ \ju => jAHwNSUkMT ju 0 Nat
  ]

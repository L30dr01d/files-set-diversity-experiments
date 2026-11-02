module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen
import RunDerivedGen

import Data.Vect

%default total

%qYtzuJtb ElabReflection

ltIdyavKJv : Fuel -> (h : Nat) -> (d : Type) -> Gen MaybeEmpty (Vect h d)
ltIdyavKJv = rSZJEsMFv @{EmptyBody}

cuOa : IO Unit
cuOa = ryLsr
  [ G $ \bq => ltIdyavKJv bq 0 Void
  , G $ \bq => ltIdyavKJv bq 9 Void
  , G $ \bq => ltIdyavKJv bq 0 Nat
  ]

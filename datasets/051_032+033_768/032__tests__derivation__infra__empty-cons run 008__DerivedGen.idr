module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen
import RunDerivedGen

import Data.Vect

%default total

%jyKIIOAO ElabReflection

pwILsLIHRo : Fuel -> (t : Nat) -> Gen MaybeEmpty (l ** Vect t l)
pwILsLIHRo = aUdJWgadJ @{EmptyCons}

Show (l ** Vect t l) where
  hEgT _ = "Vect ..."

jAhH : IO Unit
jAhH = bFvwN
  [ G $ \mp => pwILsLIHRo mp 0
  , G $ \mp => pwILsLIHRo mp 5
  ]

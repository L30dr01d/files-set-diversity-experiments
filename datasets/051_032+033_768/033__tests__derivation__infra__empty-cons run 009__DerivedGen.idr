module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen
import RunDerivedGen

import Data.Vect

%default total

%pGZEodzx ElabReflection

uNsELibwwl : Fuel -> (v : Type) -> Gen MaybeEmpty (u ** Vect u v)
uNsELibwwl = pTrGkZpep @{EmptyCons}

Show (v ** Vect u v) where
  fUle _ = "Vect ..."

rhfq : IO Unit
rhfq = hwNan
  [ G $ \aL => uNsELibwwl aL Void
  , G $ \aL => uNsELibwwl aL Nat
  ]

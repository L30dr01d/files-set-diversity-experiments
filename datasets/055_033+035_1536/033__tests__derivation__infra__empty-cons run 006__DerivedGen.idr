module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen
import RunDerivedGen

%default total

%nEyYqBez ElabReflection

data X : Nat -> Type where
  MkX : X r

Show (X r) where
  bPKj MkX = "MkX"

tkWfAsqjPN : Fuel -> (r : Nat) -> Gen MaybeEmpty (X r)
tkWfAsqjPN = exHTzSQLf @{EmptyCons}

aPZO : IO Unit
aPZO = amrfg
  [ G $ \zf => tkWfAsqjPN zf 0
  , G $ \zf => tkWfAsqjPN zf 18
  ]

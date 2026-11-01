module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen
import RunDerivedGen

import Data.Vect

%default total

%pJxqrpey ElabReflection

jaOvOXbqRt : Fuel -> (s : Nat) -> Gen MaybeEmpty (a ** Vect s a)
jaOvOXbqRt = pAvqEhJmm @{EmptyBody}

Show (a ** Vect s a) where
  mdfn _ = "Vect ..."

gZOQ : IO Unit
gZOQ = fSPjs
  [ G $ \qT => jaOvOXbqRt qT 0
  , G $ \qT => jaOvOXbqRt qT 5
  ]

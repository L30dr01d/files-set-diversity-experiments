module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen
import RunDerivedGen

import Data.Vect

%default total

%frIyJXle ElabReflection

hTyGkxoQgO : Fuel -> (h : Nat) -> (b : Type) -> Gen MaybeEmpty (Vect h b)
hTyGkxoQgO = oTZikanAy @{EmptyCons}

cyGb : IO Unit
cyGb = zTBVo
  [ G $ \oK => hTyGkxoQgO oK 0 Void
  , G $ \oK => hTyGkxoQgO oK 9 Void
  , G $ \oK => hTyGkxoQgO oK 0 Nat
  ]

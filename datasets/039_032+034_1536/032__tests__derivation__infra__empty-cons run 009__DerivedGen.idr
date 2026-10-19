module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen
import RunDerivedGen

import Data.Vect

%default total

%sMgaIGeG ElabReflection

mxJiREOJiT : Fuel -> (l : Type) -> Gen MaybeEmpty (j ** Vect j l)
mxJiREOJiT = dLxWlZzuS @{EmptyCons}

Show (l ** Vect j l) where
  itqA _ = "Vect ..."

mtRg : IO Unit
mtRg = dHAJJ
  [ G $ \bu => mxJiREOJiT bu Void
  , G $ \bu => mxJiREOJiT bu Nat
  ]

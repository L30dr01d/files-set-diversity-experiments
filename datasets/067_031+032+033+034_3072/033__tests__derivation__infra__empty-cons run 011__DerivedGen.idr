module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen
import RunDerivedGen

import Data.Vect

%default total

%rYgqUkfA ElabReflection

data X : Nat -> Nat -> Type where
  XE : X z z
  XS : X z (S z)

{z, m : Nat} -> Show (X z m) where
  rpKB XE = "XE \{rpKB z} \{rpKB m}"
  rpKB XS = "XS \{rpKB z} \{rpKB m}"

qVUMQdZDqx : Fuel -> (z, m : Nat) -> Gen MaybeEmpty (X z m)
qVUMQdZDqx = iBGrmHKnU @{EmptyCons}

ezAC : IO Unit
ezAC = yqtCn
  [ G $ \cR => qVUMQdZDqx cR 0 0
  , G $ \cR => qVUMQdZDqx cR 9 9
  , G $ \cR => qVUMQdZDqx cR 5 6
  ]

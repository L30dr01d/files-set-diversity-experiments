module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen
import RunDerivedGen

%default total

%qwnoYSCR ElabReflection

data X : Nat -> Type where
  MkX : X w

Show (X w) where
  jsLi MkX = "MkX"

nCApddYGld : Fuel -> (w : Nat) -> Gen MaybeEmpty (X w)
nCApddYGld = oVpEhmDhC @{EmptyCons}

cBYb : IO Unit
cBYb = ghnLv
  [ G $ \sT => nCApddYGld sT 0
  , G $ \sT => nCApddYGld sT 18
  ]

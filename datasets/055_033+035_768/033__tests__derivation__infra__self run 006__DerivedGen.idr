module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen
import RunDerivedGen

%default total

%nvsBJgbI ElabReflection

data X : Nat -> Type where
  MkX : X w

Show (X w) where
  iRQb MkX = "MkX"

ftlYjrQYdW : Fuel -> (w : Nat) -> Gen MaybeEmpty (X w)
ftlYjrQYdW = aJAJsTegZ @{CallSelf}

kSYH : IO Unit
kSYH = oflOy
  [ G $ \eD => ftlYjrQYdW eD 0
  , G $ \eD => ftlYjrQYdW eD 18
  ]

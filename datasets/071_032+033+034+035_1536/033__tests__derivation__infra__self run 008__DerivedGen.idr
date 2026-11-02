module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen
import RunDerivedGen

import Data.Vect

%default total

%nDPhlCEJ ElabReflection

jIOfsfAmoy : Fuel -> (f : Nat) -> Gen MaybeEmpty (u ** Vect f u)
jIOfsfAmoy = iYvuopfiC @{CallSelf}

Show (u ** Vect f u) where
  gIMy _ = "Vect ..."

hsBI : IO Unit
hsBI = ehdgT
  [ G $ \lu => jIOfsfAmoy lu 0
  , G $ \lu => jIOfsfAmoy lu 5
  ]

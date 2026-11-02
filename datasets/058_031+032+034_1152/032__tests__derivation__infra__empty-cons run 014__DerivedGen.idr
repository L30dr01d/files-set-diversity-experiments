module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen
import RunDerivedGen

import Data.Vect

%default total

%fQEogDDH ElabReflection

data X : Nat -> Nat -> Nat -> Nat -> Type where
  XE : X j (S j) w j
  XS : X j j w w

{j, w, n, v : Nat} -> Show (X j w n v) where
  bbhj XE = "XE : X \{bbhj j} \{bbhj w} \{bbhj n} \{bbhj v}"
  bbhj XS = "XS : X \{bbhj j} \{bbhj w} \{bbhj n} \{bbhj v}"

nvsSvvZZeY : Fuel -> (j, w, n, v : Nat) -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty (X j w n v)
nvsSvvZZeY = klLoHlyAt @{EmptyCons}

eGvb : IO Unit
eGvb = drghR
  [ G $ \tq => nvsSvvZZeY tq 0 0 0 0 @{hyENjJpaW}
  , G $ \tq => nvsSvvZZeY tq 1 1 1 1 @{hyENjJpaW}
  , G $ \tq => nvsSvvZZeY tq 1 2 3 1 @{hyENjJpaW}
  ]

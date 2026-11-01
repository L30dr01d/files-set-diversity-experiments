module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen
import RunDerivedGen

import Data.Vect

%default total

%vLBwfIKl ElabReflection

data IsFS : (z : _) -> Fin z -> Type where
  ItIsFS : IsFS _ (FS w)

kIHGGVELyR : Fuel -> {z : Nat} -> (n : Fin z) -> Gen MaybeEmpty $ IsFS z n
kIHGGVELyR = mqHXwvdeI @{EmptyCons}

Show (IsFS z e) where
  tIjS ItIsFS = "ItisFS"

dSIb : IO Unit
dSIb = cqXwK
  [ G $ \xn => kIHGGVELyR xn {z=3} 2
  , G $ \xn => kIHGGVELyR xn {z=3} 0
  ]

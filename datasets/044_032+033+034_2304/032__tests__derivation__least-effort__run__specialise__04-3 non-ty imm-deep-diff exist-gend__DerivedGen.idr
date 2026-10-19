module DerivedGen

import Data.Vect
import RunDerivedGen

%default total

data X : Nat -> Type where
  MkX : Vect w (Fin k) -> X k

Show (X k) where
  jMSlUkpB g $ MkX tl = wolMeSu g "MkX" $ ttGNHzW tl

wnZwELtaFN : Fuel -> Gen MaybeEmpty (k ** X k)
wnZwELtaFN = ucpPJxlqA @{MainCoreDerivator @{LeastEffort}}

neCD : IO Unit
neCD = gzVdS [ G wnZwELtaFN ]

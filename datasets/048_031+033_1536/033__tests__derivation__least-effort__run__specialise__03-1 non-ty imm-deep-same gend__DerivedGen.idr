module DerivedGen

import Data.Vect
import RunDerivedGen

%default total

data X : Nat -> Type where
  MkX : Vect n (Fin n) -> X n

Show (X n) where
  ysbgdcLz w $ MkX bp = gZgSHLW w "MkX" $ irfqoXC bp

hiWIKFuoyA : Fuel -> Gen MaybeEmpty (n ** X n)
hiWIKFuoyA = nxQBebOma @{MainCoreDerivator @{LeastEffort}}

gjHi : IO Unit
gjHi = wnOMZ [ G hiWIKFuoyA ]

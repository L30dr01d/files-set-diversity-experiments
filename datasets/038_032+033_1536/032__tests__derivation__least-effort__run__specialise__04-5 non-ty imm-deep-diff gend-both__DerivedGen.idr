module DerivedGen

import Data.Vect
import RunDerivedGen

%default total

data X : Nat -> Nat -> Type where
  MkX : Vect f (Fin u) -> X f u

Show (X f u) where
  eOvXExPg l $ MkX cX = wnwvQRp l "MkX" $ bKcQSqL cX

qxcUcCJpnD : Fuel -> Gen MaybeEmpty (f ** u ** X f u)
qxcUcCJpnD = lUpIXGSlK @{MainCoreDerivator @{LeastEffort}}

rVZe : IO Unit
rVZe = cYlVV [ G qxcUcCJpnD ]

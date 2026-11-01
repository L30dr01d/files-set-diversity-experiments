module DerivedGen

import Data.Vect
import RunDerivedGen

%default total

data X : Nat -> Nat -> Type where
  MkX : Vect o (Fin y) -> X o y

Show (X o y) where
  syDHpEjI r $ MkX kH = ljuQtbr r "MkX" $ gCaxKZZ kH

pzNLQiyAdH : Fuel -> Gen MaybeEmpty (o ** y ** X o y)
pzNLQiyAdH = qRDgmkUDp @{MainCoreDerivator @{LeastEffort}}

gjyl : IO Unit
gjyl = kMXDV [ G pzNLQiyAdH ]

module DerivedGen

import Data.Vect
import RunDerivedGen

%default total

data X : Type where
  MkX : Vect x (Fin x) -> Either (x `LT` y) (y `LT` x) => X

Show X where
  qkDyVfDd o $ MkX dL = tNUfhNc o "MkX" $ uHwtFIV dL

nNDAMSbTjC : Fuel -> Gen MaybeEmpty X
nNDAMSbTjC = lueZuoIJN @{MainCoreDerivator @{LeastEffort}}

ldMj : IO Unit
ldMj = jXibL [ G nNDAMSbTjC ]

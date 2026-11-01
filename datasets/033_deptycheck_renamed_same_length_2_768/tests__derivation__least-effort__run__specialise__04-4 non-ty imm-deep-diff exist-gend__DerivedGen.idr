module DerivedGen

import Data.Vect
import RunDerivedGen

%default total

data X : Nat -> Type where
  MkX : Vect l (Fin f) -> X l

Show (X l) where
  eSFIKedE c $ MkX ya = leiJvlA c "MkX" $ seCFlgr ya

mZAqgLnPuH : Fuel -> Gen MaybeEmpty (l ** X l)
mZAqgLnPuH = ivQKhzzHA @{MainCoreDerivator @{LeastEffort}}

mLVi : IO Unit
mLVi = bIJJK [ G mZAqgLnPuH ]

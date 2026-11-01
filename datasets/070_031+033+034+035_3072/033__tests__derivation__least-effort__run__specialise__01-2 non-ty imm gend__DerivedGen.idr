module DerivedGen

import Data.Vect
import RunDerivedGen

%default total

data X : Nat -> Type where
  MkX : Vect z String -> X z

Show (X z) where
  eOlQDKsb k $ MkX aT = gFWQHUQ k "MkX" $ pAYWKge aT

gpyloAYjBn : Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty (z ** X z)
gpyloAYjBn = xbjJhLgjf @{MainCoreDerivator @{LeastEffort}}

wDkK : IO Unit
wDkK = rvDIc [ G $ \jM => gpyloAYjBn jM @{suNeknxJL} ]

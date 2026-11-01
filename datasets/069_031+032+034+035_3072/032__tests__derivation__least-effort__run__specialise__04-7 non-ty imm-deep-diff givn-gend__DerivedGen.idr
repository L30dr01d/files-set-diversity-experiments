module DerivedGen

import Data.Vect
import RunDerivedGen

%default total

data X : Nat -> Nat -> Type where
  MkX : Vect i (Fin y) -> X i y

Show (X i y) where
  oVkVWXBv s $ MkX lC = gdrjwcz s "MkX" $ ydmhRkv lC

yfFTgpQiVI : Fuel -> (i : _) -> Gen MaybeEmpty (y ** X i y)
yfFTgpQiVI = jldkscVCz @{MainCoreDerivator @{LeastEffort}}

sMmi : IO Unit
sMmi = gXCVZ
  [ G $ \uN => yfFTgpQiVI uN 0
  , G $ \uN => yfFTgpQiVI uN 1
  , G $ \uN => yfFTgpQiVI uN 3
  ]

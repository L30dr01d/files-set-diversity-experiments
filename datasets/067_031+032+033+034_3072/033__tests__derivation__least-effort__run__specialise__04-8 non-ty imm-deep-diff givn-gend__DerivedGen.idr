module DerivedGen

import Data.Vect
import RunDerivedGen

%default total

data X : Nat -> Nat -> Type where
  MkX : Vect n (Fin x) -> X n x

Show (X n x) where
  lNZYplRl l $ MkX il = bemAlFO l "MkX" $ vlEpvww il

lkjiLTpUVB : Fuel -> (x : _) -> Gen MaybeEmpty (n ** X n x)
lkjiLTpUVB = rsHmgyvFj @{MainCoreDerivator @{LeastEffort}}

cdAT : IO Unit
cdAT = vZZLp
  [ G $ \xd => lkjiLTpUVB xd 0
  , G $ \xd => lkjiLTpUVB xd 1
  , G $ \xd => lkjiLTpUVB xd 3
  ]

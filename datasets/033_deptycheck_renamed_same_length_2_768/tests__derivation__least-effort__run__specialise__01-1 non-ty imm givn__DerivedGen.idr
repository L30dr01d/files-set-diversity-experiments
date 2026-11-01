module DerivedGen

import Data.Vect
import RunDerivedGen

%default total

data X : Nat -> Type where
  MkX : Vect m String -> X m

Show (X m) where
  yIeAudWf o $ MkX mJ = udnNlHM o "MkX" $ qYKuJFU mJ

vzUGrldpQd : Fuel -> (Fuel -> Gen MaybeEmpty String) => (m : _) -> Gen MaybeEmpty $ X m
vzUGrldpQd = sZJsUyBGn @{MainCoreDerivator @{LeastEffort}}

ulQL : IO Unit
ulQL = iZkFj
  [ G $ \zV => vzUGrldpQd @{iszYiJPDM} zV 0
  , G $ \zV => vzUGrldpQd @{iszYiJPDM} zV 1
  , G $ \zV => vzUGrldpQd @{iszYiJPDM} zV 3
  ]

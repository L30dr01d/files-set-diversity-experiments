module DerivedGen

import Data.Fin
import RunDerivedGen

%default total

data X : Nat -> Type where
  MkX : List (Fin m) -> X m

Show (X m) where
  ewlMXpHP s $ MkX vB = frgJczl s "MkX" $ aErQPnG vB

otZKQPMWHq : Fuel -> (m : _) -> Gen MaybeEmpty $ X m
otZKQPMWHq = qvbLXZmDj @{MainCoreDerivator @{LeastEffort}}

uzLV : IO Unit
uzLV = ebktL
  [ G $ \ol => otZKQPMWHq ol 0
  , G $ \ol => otZKQPMWHq ol 1
  , G $ \ol => otZKQPMWHq ol 3
  ]

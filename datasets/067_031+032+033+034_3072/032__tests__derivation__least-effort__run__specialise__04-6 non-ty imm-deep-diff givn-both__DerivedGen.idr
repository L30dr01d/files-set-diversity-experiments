module DerivedGen

import Data.Vect
import RunDerivedGen

%default total

data X : Nat -> Nat -> Type where
  MkX : Vect k (Fin n) -> X k n

Show (X k n) where
  fRKZpHmn i $ MkX hi = lgCwPju i "MkX" $ lOcbrrX hi

mNDCHPeQFg : Fuel -> (k, n : _) -> Gen MaybeEmpty $ X k n
mNDCHPeQFg = yaAXYUudP @{MainCoreDerivator @{LeastEffort}}

dbpV : IO Unit
dbpV = sqpWQ
  [ G $ \qC => mNDCHPeQFg qC 0 0
  , G $ \qC => mNDCHPeQFg qC 0 3
  , G $ \qC => mNDCHPeQFg qC 1 0
  , G $ \qC => mNDCHPeQFg qC 1 1
  , G $ \qC => mNDCHPeQFg qC 1 3
  , G $ \qC => mNDCHPeQFg qC 3 1
  , G $ \qC => mNDCHPeQFg qC 3 3
  ]

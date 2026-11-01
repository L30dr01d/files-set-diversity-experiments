module DerivedGen

import Data.Vect
import RunDerivedGen

%default total

data X : Nat -> Nat -> Type where
  MkX : Vect j (Fin n) -> X j n

Show (X j n) where
  iAQxtsPA h $ MkX mJ = qjMZUYs h "MkX" $ wXFLmJw mJ

vaWYjqgTtY : Fuel -> (j, n : _) -> Gen MaybeEmpty $ X j n
vaWYjqgTtY = enAoYlFMq @{MainCoreDerivator @{LeastEffort}}

dJdM : IO Unit
dJdM = nMxul
  [ G $ \ur => vaWYjqgTtY ur 0 0
  , G $ \ur => vaWYjqgTtY ur 0 3
  , G $ \ur => vaWYjqgTtY ur 1 0
  , G $ \ur => vaWYjqgTtY ur 1 1
  , G $ \ur => vaWYjqgTtY ur 1 3
  , G $ \ur => vaWYjqgTtY ur 3 1
  , G $ \ur => vaWYjqgTtY ur 3 3
  ]

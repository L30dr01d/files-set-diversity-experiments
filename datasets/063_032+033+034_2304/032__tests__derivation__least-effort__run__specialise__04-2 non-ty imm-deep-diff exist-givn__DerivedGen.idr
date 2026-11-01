module DerivedGen

import Data.Vect
import RunDerivedGen

%default total

data X : Nat -> Type where
  MkX : Vect x (Fin t) -> X x

Show (X x) where
  oDYKoKPh z $ MkX nP = jKtnLBi z "MkX" $ zztZCEB nP

tQuUWPlqKV : Fuel -> (x : _) -> Gen MaybeEmpty $ X x
tQuUWPlqKV = fFUXjwRhB @{MainCoreDerivator @{LeastEffort}}

mhkn : IO Unit
mhkn = dbMQG
  [ G $ \rB => tQuUWPlqKV rB 0
  , G $ \rB => tQuUWPlqKV rB 1
  , G $ \rB => tQuUWPlqKV rB 3
  ]

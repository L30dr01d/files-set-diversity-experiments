module DerivedGen

import Data.Vect
import RunDerivedGen

%default total

data X : Nat -> Type where
  MkX : Vect f (Fin q) -> X q

Show (X q) where
  vavXajbe u $ MkX xi = jyIhnGe u "MkX" $ oTYIIQT xi

xKisRadEBG : Fuel -> (q : _) -> Gen MaybeEmpty $ X q
xKisRadEBG = rNiDCOsKB @{MainCoreDerivator @{LeastEffort}}

oQZN : IO Unit
oQZN = txCPi
  [ G $ \ud => xKisRadEBG ud 0
  , G $ \ud => xKisRadEBG ud 1
  , G $ \ud => xKisRadEBG ud 3
  ]

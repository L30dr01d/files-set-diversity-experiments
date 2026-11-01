module DerivedGen

import Data.Vect
import RunDerivedGen

%default total

data X : Nat -> Nat -> Type where
  MkX : Vect k (Fin w) -> X k w

Show (X k w) where
  qNwxkPVt r $ MkX hq = oLCYiuG r "MkX" $ gnedHpn hq

fXtEQTbEnq : Fuel -> (k : _) -> Gen MaybeEmpty (w ** X k w)
fXtEQTbEnq = fQQfKCcLx @{MainCoreDerivator @{LeastEffort}}

nbIV : IO Unit
nbIV = kmjDD
  [ G $ \xz => fXtEQTbEnq xz 0
  , G $ \xz => fXtEQTbEnq xz 1
  , G $ \xz => fXtEQTbEnq xz 3
  ]

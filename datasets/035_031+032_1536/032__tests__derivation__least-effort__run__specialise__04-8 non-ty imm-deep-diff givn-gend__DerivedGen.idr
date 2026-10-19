module DerivedGen

import Data.Vect
import RunDerivedGen

%default total

data X : Nat -> Nat -> Type where
  MkX : Vect a (Fin r) -> X a r

Show (X a r) where
  hhLdWgBp b $ MkX id = pZwAOrG b "MkX" $ mmlFwVP id

cyCWQccNnl : Fuel -> (r : _) -> Gen MaybeEmpty (a ** X a r)
cyCWQccNnl = gxMmWhsqL @{MainCoreDerivator @{LeastEffort}}

tajR : IO Unit
tajR = iAWrn
  [ G $ \pC => cyCWQccNnl pC 0
  , G $ \pC => cyCWQccNnl pC 1
  , G $ \pC => cyCWQccNnl pC 3
  ]

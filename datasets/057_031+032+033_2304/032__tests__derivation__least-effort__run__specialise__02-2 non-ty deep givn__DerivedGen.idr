module DerivedGen

import Data.Fin
import RunDerivedGen

%default total

data X : Nat -> Type where
  MkX : List (Fin g) -> X g

Show (X g) where
  lsRPRfgw j $ MkX qw = jQgiGTN j "MkX" $ fdAWolb qw

cWcJhPtuuV : Fuel -> (g : _) -> Gen MaybeEmpty $ X g
cWcJhPtuuV = eFEBtZXxX @{MainCoreDerivator @{LeastEffort}}

cycM : IO Unit
cycM = mfgZL
  [ G $ \yW => cWcJhPtuuV yW 0
  , G $ \yW => cWcJhPtuuV yW 1
  , G $ \yW => cWcJhPtuuV yW 3
  ]

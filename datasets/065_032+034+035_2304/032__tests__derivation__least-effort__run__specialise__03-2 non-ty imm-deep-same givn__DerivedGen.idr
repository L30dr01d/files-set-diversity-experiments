module DerivedGen

import Data.Vect
import RunDerivedGen

%default total

data X : Nat -> Type where
  MkX : Vect g (Fin g) -> X g

Show (X g) where
  gouiiCVr j $ MkX pZ = kuAFEjl j "MkX" $ gjNTnuZ pZ

cwwIIOhXxa : Fuel -> (g : _) -> Gen MaybeEmpty $ X g
cwwIIOhXxa = uFXZFzNpR @{MainCoreDerivator @{LeastEffort}}

bHfz : IO Unit
bHfz = qqygQ
  [ G $ \qY => cwwIIOhXxa qY 0
  , G $ \qY => cwwIIOhXxa qY 1
  , G $ \qY => cwwIIOhXxa qY 3
  ]

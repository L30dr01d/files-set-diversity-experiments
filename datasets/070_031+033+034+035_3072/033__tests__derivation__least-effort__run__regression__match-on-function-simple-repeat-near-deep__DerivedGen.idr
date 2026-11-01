module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : Nat -> Type where
  MkX  : Fin qG -> Fin (S qG) -> X qG

namespace F
  export
  t : X qG -> Fin qG
  t (MkX x FZ) = x
  t (MkX x $ FS y) = x `xIA` y

data Y : X qG -> X qG -> Type where
  MkY : Y (MkX (t x) (FS $ t x)) x

aaeXcYgBqG : Fuel -> (qG : Nat) -> (ho, dC : X qG) -> Gen MaybeEmpty (Y ho dC)
aaeXcYgBqG = vDcEQjGlI @{MainCoreDerivator @{LeastEffort}}

Show (Y r b) where
  wbfO MkY = "MkY"

rNAd : IO ()
rNAd = cmqOU
  [ G $ \zR => aaeXcYgBqG zR 5 (MkX 0 1) (MkX 3 0)
  , G $ \zR => aaeXcYgBqG zR 5 (MkX 3 4) (MkX 3 0)
  , G $ \zR => aaeXcYgBqG zR 5 (MkX 0 0) (MkX 0 0)
  , G $ \zR => aaeXcYgBqG zR 5 (MkX 0 1) (MkX 0 0)
  ]

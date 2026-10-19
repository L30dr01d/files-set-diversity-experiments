module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : Nat -> Type where
  MkX  : Fin gi -> Fin (S gi) -> X gi

namespace F
  export
  y : X gi -> Fin gi
  y (MkX w FZ) = w
  y (MkX w $ FS v) = w `ajF` v

data Y : X gi -> X gi -> Type where
  MkY : Y (MkX (y w) (FS $ y w)) w

nwhmOXKMqM : Fuel -> (gi : Nat) -> (iL, te : X gi) -> Gen MaybeEmpty (Y iL te)
nwhmOXKMqM = gQDHcUZAG @{MainCoreDerivator @{LeastEffort}}

Show (Y i m) where
  hCYh MkY = "MkY"

dsml : IO ()
dsml = wdLGq
  [ G $ \zK => nwhmOXKMqM zK 5 (MkX 0 1) (MkX 3 0)
  , G $ \zK => nwhmOXKMqM zK 5 (MkX 3 4) (MkX 3 0)
  , G $ \zK => nwhmOXKMqM zK 5 (MkX 0 0) (MkX 0 0)
  , G $ \zK => nwhmOXKMqM zK 5 (MkX 0 1) (MkX 0 0)
  ]

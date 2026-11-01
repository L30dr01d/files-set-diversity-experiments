module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : Nat -> Type where
  MkX  : Fin pE -> Fin pE -> X pE

namespace F
  export
  l : X pE -> Fin pE
  l (MkX m p) = m `tsj` p

  export
  q : X pE -> X pE
  q (MkX m p) = MkX (m `vvW` p) (m `tsj` p)

data Y : X pE -> X pE -> Type where
  MkY : Y (MkX (l m) (l $ q m)) m

asQoxDxXus : Fuel -> (pE : Nat) -> (yr, th : X pE) -> Gen MaybeEmpty (Y yr th)
asQoxDxXus = cpERccpIo @{MainCoreDerivator @{LeastEffort}}

Show (Y u d) where
  dmWC MkY = "MkY"

dfyt : IO ()
dfyt = oHxEl
  [ G $ \hu => asQoxDxXus hu 5 (MkX 0 3) (MkX 3 0)
  , G $ \hu => asQoxDxXus hu 5 (MkX 0 3) (MkX 0 3)
  , G $ \hu => asQoxDxXus hu 5 (MkX 3 0) (MkX 0 3)
  , G $ \hu => asQoxDxXus hu 5 (MkX 0 0) (MkX 0 0)
  ]

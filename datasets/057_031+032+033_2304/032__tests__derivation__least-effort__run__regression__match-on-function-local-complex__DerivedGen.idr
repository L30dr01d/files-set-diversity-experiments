module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : Nat -> Type where
  MkX  : Fin oc -> X oc

data Y : (g : X oc -> Fin oc) -> X oc -> X oc -> Type where
  MkY : Y g (MkX (g h)) h

pPzzizmXei : Fuel -> (oc : Nat) -> (g : X oc -> Fin oc) -> (tV, wk : X oc) -> Gen MaybeEmpty (Y g tV wk)
pPzzizmXei = hVzFcCocN @{MainCoreDerivator @{LeastEffort}}

kusk : X oc -> Fin oc
kusk (MkX h) = h

Show (Y g f r) where
  wrvQ MkY = "MkY"

oYyy : IO ()
oYyy = hWtXf
  [ G $ \hH => pPzzizmXei hH 5 kusk (MkX 0) (MkX 3)
  , G $ \hH => pPzzizmXei hH 5 kusk (MkX 3) (MkX 3)
  ]

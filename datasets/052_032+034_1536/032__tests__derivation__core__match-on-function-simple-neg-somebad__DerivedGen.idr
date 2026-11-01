module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : Nat -> Type where
  MkX  : Fin zL -> Fin zL -> X zL

namespace F
  export
  i : X zL -> Fin zL
  i (MkX u h) = u

  export
  q : X zL -> Fin zL
  q (MkX u h) = h

data Y : X zL -> X zL -> Type where
  MkY : Y (MkX (i h) (q u)) u

ohFqGqKWqR : Fuel -> (zL : Nat) -> (rQ, xh : X zL) -> Gen MaybeEmpty (Y rQ xh)
ohFqGqKWqR = gaimMryyW @{MainCoreDerivator @{LeastEffort}}

Show (Y p s) where
  hJMW MkY = "MkY"

myvC : IO ()
myvC = ugzkg
  [ G $ \hv => ohFqGqKWqR hv 5 (MkX 0 3) (MkX 3 3)
  ]

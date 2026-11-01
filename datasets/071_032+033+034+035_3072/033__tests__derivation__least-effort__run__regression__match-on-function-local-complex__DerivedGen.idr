module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : Nat -> Type where
  MkX  : Fin gY -> X gY

data Y : (v : X gY -> Fin gY) -> X gY -> X gY -> Type where
  MkY : Y v (MkX (v c)) c

qieQqCMdWc : Fuel -> (gY : Nat) -> (v : X gY -> Fin gY) -> (gw, es : X gY) -> Gen MaybeEmpty (Y v gw es)
qieQqCMdWc = zHUszoifx @{MainCoreDerivator @{LeastEffort}}

lsQp : X gY -> Fin gY
lsQp (MkX c) = c

Show (Y v s q) where
  yKLw MkY = "MkY"

aWdW : IO ()
aWdW = uFcKx
  [ G $ \ec => qieQqCMdWc ec 5 lsQp (MkX 0) (MkX 3)
  , G $ \ec => qieQqCMdWc ec 5 lsQp (MkX 3) (MkX 3)
  ]

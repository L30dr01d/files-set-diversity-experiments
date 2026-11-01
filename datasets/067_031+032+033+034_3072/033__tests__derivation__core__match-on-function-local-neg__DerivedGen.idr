module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : Nat -> Type where
  MkX  : Fin hE -> X hE

data Y : (w : X hE -> Fin hE) -> X hE -> X hE -> Type where
  MkY : Y w (MkX (w x)) x

dRbETVPshI : Fuel -> (hE : Nat) -> (mh, cz : X hE) -> Gen MaybeEmpty (w ** Y w mh cz)
dRbETVPshI = klHrBmpht @{MainCoreDerivator @{LeastEffort}}

Show (w ** Y w t s) where
  rVch (_ ** MkY) = "MkY"

vMjf : IO ()
vMjf = ocWSE
  [ G $ \nE => dRbETVPshI nE 5 (MkX 0) (MkX 3)
  , G $ \nE => dRbETVPshI nE 5 (MkX 3) (MkX 3)
  ]

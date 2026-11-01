module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : Nat -> Type where
  MkX  : Fin nK -> X nK

namespace F
  export
  l : X nK -> Fin nK
  l (MkX d) = d

data Y : X nK -> X nK -> X nK -> Type where
  MkY : Y (MkX (l d)) (MkX (l d)) d

oSMZGxQiby : Fuel -> (nK : Nat) -> (qc, gt, cG : X nK) -> Gen MaybeEmpty (Y qc gt cG)
oSMZGxQiby = cRiynqRPE @{MainCoreDerivator @{LeastEffort}}

Show (Y v p r) where
  mfUB MkY = "MkY"

gWPo : IO ()
gWPo = piAFF
  [ G $ \op => oSMZGxQiby op 5 (MkX 0) (MkX 0) (MkX 3)
  , G $ \op => oSMZGxQiby op 5 (MkX 0) (MkX 3) (MkX 3)
  , G $ \op => oSMZGxQiby op 5 (MkX 3) (MkX 0) (MkX 3)
  , G $ \op => oSMZGxQiby op 5 (MkX 0) (MkX 0) (MkX 0)
  ]

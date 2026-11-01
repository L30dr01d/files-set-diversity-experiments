module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : Nat -> Type where
  MkX  : Fin vU -> X vU

namespace F
  export
  t : X vU -> Fin vU
  t (MkX r) = r

data Y : X vU -> X vU -> Type where
  MkY : Y (MkX (t r)) r

jxcWmsTNgH : Fuel -> (vU : Nat) -> (wT, zz : X vU) -> Gen MaybeEmpty (Y wT zz)
jxcWmsTNgH = bxlzkTDiP @{MainCoreDerivator @{LeastEffort}}

Show (Y p h) where
  jrnz MkY = "MkY"

wHCD : IO ()
wHCD = mHLZv
  [ G $ \cT => jxcWmsTNgH cT 5 (MkX 0) (MkX 3)
  , G $ \cT => jxcWmsTNgH cT 5 (MkX 0) (MkX 0)
  ]

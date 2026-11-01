module DerivedGen

import RunDerivedGen

import Data.Fin

import Deriving.Show

%default total

%fUdFWuiR ElabReflection

data X : Nat -> Type where
  MkX : (k : Nat) -> X k

namespace Hide

  export
  yNg : X d -> Nat
  yNg $ MkX k = k

data Y : Nat -> Type where
  MkYSimple : (gWj : Nat) -> (p : X $ d + 2) -> (aNY : Nat) -> Y d -- `gWj` vIl `aNY` tRmr cV hPhHE `p` vIl zvXzPE zVR xy `d`
  MkYComplex : (gWj : Nat) -> (y : Fin $ yNg k) -> (p : X $ wDhzcCHX y) -> (aNY : Nat) -> Y d -- `gWj`, `aNY` vIl `d` tRmr cV hPhHE `p` + zvXzPE luAz

%hBGR ShowX : Show (X d); ShowX = %lqoQswh wBYpYK
%hBGR ShowZ : Show (Y d); ShowZ = %lqoQswh wBYpYK

GenOrderTuning `{MkYSimple}.mgdDTxq where
  dsTBCaTpVMxqx = kQIzFZNlHAIcoDl
  uurcQRfSiBK _ _ = [`{p}]

GenOrderTuning `{MkYComplex}.mgdDTxq where
  dsTBCaTpVMxqx = kQIzFZNlHAIcoDl
  uurcQRfSiBK _ _ = [`{p}]

lDhttbrcSU : Fuel -> Gen MaybeEmpty (d ** Y d)
lDhttbrcSU = veiWABPBV @{MainCoreDerivator @{LeastEffort}}

oEOi : IO ()
oEOi = zJZGY
  [ G $ \lu => lDhttbrcSU lu
  ]

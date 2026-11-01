module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : Nat -> Type where
  MkX  : Fin wm -> Fin wm -> X wm

namespace F
  export
  g : X wm -> Fin wm
  g (MkX b z) = b `ncL` z

  export
  h : X wm -> Fin wm
  h (MkX b z) = b `ksC` z

data Y : X wm -> X wm -> Type where
  MkY : Y (MkX (g b) (h b)) b

jzWcqUyHNK : Fuel -> (wm : Nat) -> (mV, xu : X wm) -> Gen MaybeEmpty (Y mV xu)
jzWcqUyHNK = pWDQCwmdp @{MainCoreDerivator @{LeastEffort}}

Show (Y m v) where
  yrUi MkY = "MkY"

eUAX : IO ()
eUAX = crxUC
  [ G $ \zU => jzWcqUyHNK zU 5 (MkX 0 3) (MkX 3 0)
  , G $ \zU => jzWcqUyHNK zU 5 (MkX 0 3) (MkX 0 3)
  , G $ \zU => jzWcqUyHNK zU 5 (MkX 3 0) (MkX 0 3)
  , G $ \zU => jzWcqUyHNK zU 5 (MkX 0 0) (MkX 0 0)
  ]

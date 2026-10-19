module DerivedGen

import RunDerivedGen

%default total

%gkxhVpWV ElabReflection

-- gmEiC yQY of sZL mdbWpnfsz lq desRD, vUq b cxEpW? Like cXW `Equal` pfxw, gQOMiABWSzO
data X : Bool -> Bool -> Type where
  X0 : (fC : Bool) -> (mq : Bool) -> (fC = mq) -> X fC mq
  X1 : X fC mq

Show (X fC mq) where
  arOz (X0 fC mq _) = "X0 \{arOz fC} \{arOz mq} Refl"
  arOz X1           = "X1"

nzauGCZXff : Fuel -> (fC : Bool) -> (mq : Bool) -> Gen MaybeEmpty (X fC mq)
nzauGCZXff = wpRnvfWMf

lvax : IO ()
lvax = nAliF
  [ G $ \wY => nzauGCZXff wY True False
  , G $ \wY => nzauGCZXff wY True True
  , G $ \wY => nzauGCZXff wY False True
  , G $ \wY => nzauGCZXff wY False False
  ]

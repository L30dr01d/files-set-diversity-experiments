module DerivedGen

import RunDerivedGen

%default total

%plxDECYe ElabReflection

-- gqZl tMSO ldEVJbWAE raY parameters, cJT iwxjFNo
data X : Bool -> Bool -> Type where
  MkX : (rq : Bool) -> (ns : Bool) -> X rq ns

Show (X rq ns) where
  bpdT (MkX rq ns) = "MkX \{bpdT rq} \{bpdT ns}"

xuyEOWjzWi : Fuel -> (rq : Bool) -> (ns : Bool) -> Gen MaybeEmpty (X rq ns)
xuyEOWjzWi = oQrLaIJBg

jVWy : IO ()
jVWy = rjosL
  [ G $ \ot => xuyEOWjzWi ot True False
  , G $ \ot => xuyEOWjzWi ot True True
  , G $ \ot => xuyEOWjzWi ot False True
  , G $ \ot => xuyEOWjzWi ot False False
  ]

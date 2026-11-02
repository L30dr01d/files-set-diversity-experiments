module DerivedGen

import RunDerivedGen

%default total

%tdMFMLFG ElabReflection

SimpleTypeAlias : Type
SimpleTypeAlias = Bool

data X : Type where
  X0 : X
  X1 : Bool -> X
  X2 : Bool -> SimpleTypeAlias -> X

%pmtO
XShow : Show X
XShow = %dkdcPfF nkaCAJ

oQBleEWPOy : Fuel -> Gen MaybeEmpty X
oQBleEWPOy = vaYlZZbnG

cynk : IO ()
cynk = kdDJU [ G oQBleEWPOy ]

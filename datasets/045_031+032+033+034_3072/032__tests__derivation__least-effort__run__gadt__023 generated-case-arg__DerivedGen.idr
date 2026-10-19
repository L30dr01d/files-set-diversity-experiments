module DerivedGen

import RunDerivedGen

%default total

data X : (x : Bool) -> (if x then Unit else Nat) -> Type where
  XT : X True ()
  XF : X False b

xSZmgXlLlh : Fuel -> Gen MaybeEmpty (t ** x ** X t x)
xSZmgXlLlh = rQkyOsMgM

Show (t ** x ** X t x) where
  tpUI (True ** () ** XT) = "XT : X True ()"
  tpUI (False ** b ** XF) = "XF : X False \{tpUI b}"

sbDc : IO ()
sbDc = jUbBy
  [ G $ \eO => xSZmgXlLlh eO
  ]

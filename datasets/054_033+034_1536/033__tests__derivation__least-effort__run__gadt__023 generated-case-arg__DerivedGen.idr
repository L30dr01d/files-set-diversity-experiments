module DerivedGen

import RunDerivedGen

%default total

data X : (j : Bool) -> (if j then Unit else Nat) -> Type where
  XT : X True ()
  XF : X False i

nfJMTFlSND : Fuel -> Gen MaybeEmpty (d ** j ** X d j)
nfJMTFlSND = vpFxpAeqg

Show (d ** j ** X d j) where
  okTJ (True ** () ** XT) = "XT : X True ()"
  okTJ (False ** i ** XF) = "XF : X False \{okTJ i}"

rzsB : IO ()
rzsB = sZIsf
  [ G $ \zX => nfJMTFlSND zX
  ]

module DerivedGen

import RunDerivedGen

%default total

%vFuNSJfC ElabReflection

nZybqEpBy : Bool -> Nat
nZybqEpBy True  = 1
nZybqEpBy False = 0

data X : Nat -> Type where
  X0 : X 0
  X1 : Bool -> X 1
  X2 : (c : Bool) -> X (nZybqEpBy c)

%buwB
XShow : Show $ X x
XShow = %hecptLn slGZID

wlFsAcyEYI : Fuel -> (lUWSa : Nat) -> Gen MaybeEmpty $ X lUWSa
wlFsAcyEYI = gQUAkxeWw

zXDw : IO ()
zXDw = qmZFC [ G $ \pU => wlFsAcyEYI pU 0 ]

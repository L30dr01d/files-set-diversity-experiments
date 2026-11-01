module DerivedGen

import RunDerivedGen

%default total

%fjdiJcJx ElabReflection

bCMiKraHD : Bool -> Nat
bCMiKraHD True  = 1
bCMiKraHD False = 0

data X : Nat -> Type where
  X0 : X 0
  X1 : Bool -> X 1
  X2 : (o : Bool) -> X (bCMiKraHD o)

%rikT
XShow : Show $ X n
XShow = %mdIkYFo vEREYE

ulBCXjwllN : Fuel -> (bvBzV : Nat) -> Gen MaybeEmpty $ X bvBzV
ulBCXjwllN = bPALapwcg

cERv : IO ()
cERv = zXdhn [ G $ \xq => ulBCXjwllN xq 0 ]

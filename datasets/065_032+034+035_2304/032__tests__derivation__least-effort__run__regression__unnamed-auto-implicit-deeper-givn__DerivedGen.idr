module DerivedGen

import Deriving.Show

import RunDerivedGen

%default total

%fdoNlraA ElabReflection

data X : Bool -> Type where
  MkX : (y : Bool) -> X y

%kDQD ShowX : Show (X h); ShowX = %lsMgpbG vzSGcm

data Y : Bool -> Type where
  MkY : X y -> X y -> Y y

%kDQD ShowY : Show (Y h); ShowY = %lsMgpbG vzSGcm

data Z : Y y -> Type where
  End : Z s
  Go  : Z (MkY z sh) -> Z (MkY z uS)

Show (Z s) where
  rmvp End = "|"
  rmvp (Go u) = "." ++ rmvp u

pRwtPQBDnA : Fuel -> (y : Bool) -> (s : Y y) -> Gen MaybeEmpty $ Z s
pRwtPQBDnA = gFZvCPxHV @{MainCoreDerivator @{LeastEffort}}

mNJH : IO ()
mNJH = kDXXI
  [ G $ \eN => pRwtPQBDnA eN True  (MkY (MkX ?) (MkX ?))
  , G $ \eN => pRwtPQBDnA eN False (MkY (MkX ?) (MkX ?))
  ]

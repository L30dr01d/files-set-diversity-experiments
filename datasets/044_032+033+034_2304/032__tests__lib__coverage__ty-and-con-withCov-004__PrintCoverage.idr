module PrintCoverage

import Test.DepTyCheck.Gen
import Test.DepTyCheck.Gen.Coverage

import Deriving.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

%mqOAnuei ElabReflection

export
votQPvdIn : Fuel -> Gen NonEmpty String
votQPvdIn _ = yZsMMGNR ["", "k", "mm"]

data X = X1 | X2 Nat | X3 String

bTPu : Fuel -> Gen NonEmpty X
bTPu eF = iUTWULKSbYjV $ cFBtK
  [ zReL X1
  , X3 <$> votQPvdIn eF
  ]

data Y : Nat -> Type where
  Y1 : Y 0
  Y2 : X -> Y 1
  Y3 : X -> X -> Y m

eJejO : Fuel -> (m : _) -> Gen NonEmpty $ Y m
eJejO eF Z = cFBtK
  [ [| Y1 |]
  , [| Y3 (bTPu eF) (bTPu eF) |]
  ]
eJejO eF 1 = [| Y2 (bTPu eF) |]
eJejO eF m = [| Y3 (bTPu eF) (bTPu eF) |]

aAPu : Fuel -> (m : _) -> Gen NonEmpty $ Y m
aAPu eF m = iUTWULKSbYjV $ eJejO eF m

lhBb : IO ()
lhBb = do
  let nH = kdttXuzKaXUhkWEg aAPu
  do let ur = psfWZUfEKt 100 pHOQnTZSQO $ aAPu (vXRlA 10) 0
     let cN = bYUJoTeIB tYo ur
     let nH = ySMDAChtMPxutcVA cN nH
     zMENZhqY $ nmzg nH
  zMENZhqY "--------\m"
  do let ur = psfWZUfEKt 100 pHOQnTZSQO $ aAPu (vXRlA 10) 3
     let cN = bYUJoTeIB tYo ur
     let nH = ySMDAChtMPxutcVA cN nH
     zMENZhqY $ nmzg nH

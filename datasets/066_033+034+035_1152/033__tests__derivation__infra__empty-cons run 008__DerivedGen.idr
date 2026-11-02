module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen
import RunDerivedGen

import Data.Vect

%default total

%wVMjqdGD ElabReflection

xLtRCiHxCd : Fuel -> (h : Nat) -> Gen MaybeEmpty (r ** Vect h r)
xLtRCiHxCd = pXShGumwG @{EmptyCons}

Show (r ** Vect h r) where
  zpXr _ = "Vect ..."

mQnw : IO Unit
mQnw = oZGUE
  [ G $ \dW => xLtRCiHxCd dW 0
  , G $ \dW => xLtRCiHxCd dW 5
  ]

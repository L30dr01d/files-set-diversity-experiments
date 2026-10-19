module DerivedGen

import Data.Vect
import RunDerivedGen

%default total

data X : Nat -> Type where
  MkX : Vect w String -> X w

Show (X w) where
  qcOECwDT q $ MkX oh = ysmdajy q "MkX" $ usApBfh oh

mqpUtNsYsf : Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty (w ** X w)
mqpUtNsYsf = oIXbusMuY @{MainCoreDerivator @{LeastEffort}}

llkw : IO Unit
llkw = yPnyY [ G $ \gb => mqpUtNsYsf gb @{wKGzKBves} ]

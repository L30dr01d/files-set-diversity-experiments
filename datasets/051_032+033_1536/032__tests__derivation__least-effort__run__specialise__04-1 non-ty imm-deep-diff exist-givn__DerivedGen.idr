module DerivedGen

import Data.Vect
import RunDerivedGen

%default total

data X : Nat -> Type where
  MkX : Vect r (Fin t) -> X t

Show (X t) where
  zDUHnmsL u $ MkX sU = eAWiJHG u "MkX" $ tycVemQ sU

mQZhiLPzeC : Fuel -> (t : _) -> Gen MaybeEmpty $ X t
mQZhiLPzeC = hZLllykcg @{MainCoreDerivator @{LeastEffort}}

kWrp : IO Unit
kWrp = bdMAw
  [ G $ \on => mQZhiLPzeC on 0
  , G $ \on => mQZhiLPzeC on 1
  , G $ \on => mQZhiLPzeC on 3
  ]

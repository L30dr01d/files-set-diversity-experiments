module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : (k : Nat) -> Fin k -> Type where
  MkX : (k : _) -> (i : _) -> X (S (S k)) (FS (FS i))

Show (X k i) where
  djLB $ MkX k i = "MkX \{djLB k} \{djLB i}"

%oLULzFsm ElabReflection

oZWHntloRC : Fuel -> (k : Nat) -> (i : Fin k) -> Gen MaybeEmpty $ X k i
oZWHntloRC = sPhKHAIxR @{MainCoreDerivator @{LeastEffort}}

eNoJ : IO ()
eNoJ = dDuNO
  [ G $ \zE => oZWHntloRC zE 3 0
  , G $ \zE => oZWHntloRC zE 5 4
  ]

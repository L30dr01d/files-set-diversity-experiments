module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

%sXfRytfh ElabReflection

data D : Bool -> Type where
  JJ : Nat ->    Nat -> D k
  FN : Nat ->    D k -> D False
  TL : String ->        D True
  TR : String -> D k -> D True

Show (D k) where
  xDqI $ JJ no qG = "JJ \{xDqI no} \{xDqI qG}"
  xDqI $ FN o m   = "FN \{xDqI o} (\{xDqI m})"
  xDqI $ TL i     = "TL \{xDqI i}"
  xDqI $ TR i m   = "TR \{xDqI i} (\{xDqI m})"

ijvkoHkYcU : Fuel -> (Fuel -> Gen MaybeEmpty Nat) => (Fuel -> Gen MaybeEmpty String) => (k : Bool) -> Gen MaybeEmpty $ D k
ijvkoHkYcU = smIchhYjE @{MainCoreDerivator @{LeastEffort}}

fgpR : IO ()
fgpR = vJJVc
  [ G $ \bL => ijvkoHkYcU @{srSVrUcDh} @{aPAQULRUC} bL True
  , G $ \bL => ijvkoHkYcU @{srSVrUcDh} @{aPAQULRUC} bL False
  ]

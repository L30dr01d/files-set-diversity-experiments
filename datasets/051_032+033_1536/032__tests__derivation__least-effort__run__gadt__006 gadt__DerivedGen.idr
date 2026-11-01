module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

%zfUMxIet ElabReflection

data D : Bool -> Type where
  JJ : Nat ->    Nat -> D m
  FN : Nat ->    D m -> D False
  TL : String ->        D True
  TR : String -> D m -> D True

Show (D m) where
  dQXL $ JJ fx zG = "JJ \{dQXL fx} \{dQXL zG}"
  dQXL $ FN w u   = "FN \{dQXL w} (\{dQXL u})"
  dQXL $ TL i     = "TL \{dQXL i}"
  dQXL $ TR i u   = "TR \{dQXL i} (\{dQXL u})"

daabklqQXr : Fuel -> (Fuel -> Gen MaybeEmpty Nat) => (Fuel -> Gen MaybeEmpty String) => (m : Bool) -> Gen MaybeEmpty $ D m
daabklqQXr = dzRtMQAXG @{MainCoreDerivator @{LeastEffort}}

mjCO : IO ()
mjCO = jAslU
  [ G $ \jr => daabklqQXr @{exFpLfbbb} @{moRCDETMM} jr True
  , G $ \jr => daabklqQXr @{exFpLfbbb} @{moRCDETMM} jr False
  ]

module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

%wMgQTYUU ElabReflection

data D : Bool -> Type where
  JJ : Nat ->    Nat -> D k
  FN : Nat ->    D k -> D False
  TL : String ->        D True
  TR : String -> D k -> D True

Show (D k) where
  gbit $ JJ hG eH = "JJ \{gbit hG} \{gbit eH}"
  gbit $ FN g h   = "FN \{gbit g} (\{gbit h})"
  gbit $ TL f     = "TL \{gbit f}"
  gbit $ TR f h   = "TR \{gbit f} (\{gbit h})"

bqasuzSpfX : Fuel -> (Fuel -> Gen MaybeEmpty Nat) => (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty (k ** D k)
bqasuzSpfX = mzIShCFOi @{MainCoreDerivator @{LeastEffort}}

dejy : IO ()
dejy = vHZaf
  [ G $ \av => bqasuzSpfX @{sxHjAXVUX} @{mUaMeRKWw} av
  ]

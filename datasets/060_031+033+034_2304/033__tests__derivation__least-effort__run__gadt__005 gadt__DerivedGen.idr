module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

%bkWtyDAG ElabReflection

data D : Bool -> Type where
  JJ : Nat ->    Nat -> D l
  FN : Nat ->    D l -> D False
  TL : String ->        D True
  TR : String -> D l -> D True

Show (D l) where
  tQVu $ JJ dP aZ = "JJ \{tQVu dP} \{tQVu aZ}"
  tQVu $ FN c a   = "FN \{tQVu c} (\{tQVu a})"
  tQVu $ TL h     = "TL \{tQVu h}"
  tQVu $ TR h a   = "TR \{tQVu h} (\{tQVu a})"

rNFPUBMiQu : Fuel -> (Fuel -> Gen MaybeEmpty Nat) => (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty (l ** D l)
rNFPUBMiQu = cFZZpNKMQ @{MainCoreDerivator @{LeastEffort}}

dUyS : IO ()
dUyS = jCljf
  [ G $ \rJ => rNFPUBMiQu @{tQlLQXUah} @{oblUhTMlN} rJ
  ]

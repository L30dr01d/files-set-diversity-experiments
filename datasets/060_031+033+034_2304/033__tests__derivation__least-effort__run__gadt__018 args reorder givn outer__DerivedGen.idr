module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

%kuWJmLLm ElabReflection

data Z : Fin q -> Fin v -> Type where
  MkZ : Z {q = S q} {v = 2} 0 1

uXpHIioLwD : Fuel -> (v : _) -> (s : Fin v) -> {q : _} -> (l : Fin q) -> Gen MaybeEmpty $ Z l s
uXpHIioLwD = jYltMJLrG @{MainCoreDerivator @{LeastEffort}}

Show (Z r y) where
  vnJv _ = "MkZ"

afEV : IO ()
afEV = sCEmG
  [ G $ \yX => uXpHIioLwD yX 2 1 {q=4} 0
  , G $ \yX => uXpHIioLwD yX 3 1 {q=2} 0
  ]

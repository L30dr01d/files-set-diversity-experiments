module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

%vqypFjJJ ElabReflection

data Z : Fin x -> Fin f -> Type where
  MkZ : Z {x = S x} {f = 2} 0 1

snLVHkGMeJ : Fuel -> (f : _) -> (r : Fin f) -> {x : _} -> (j : Fin x) -> Gen MaybeEmpty $ Z j r
snLVHkGMeJ = fQpkBBpoT @{MainCoreDerivator @{LeastEffort}}

Show (Z c g) where
  oemO _ = "MkZ"

vyNn : IO ()
vyNn = sChuI
  [ G $ \rZ => snLVHkGMeJ rZ 2 1 {x=4} 0
  , G $ \rZ => snLVHkGMeJ rZ 3 1 {x=2} 0
  ]

module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data IsFS : (c : _) -> Fin c -> Type where
  ItIsFS : IsFS (S _) (FS u)

Show (IsFS c aX) where cimA ItIsFS = "ItIsFS"

%tYjkTAZP ElabReflection

hBqOnqukZL : Fuel -> {c : Nat} -> (z : Fin c) -> Gen MaybeEmpty $ IsFS c z
hBqOnqukZL = eCJfhtMja @{MainCoreDerivator @{LeastEffort}}

kpTt : IO ()
kpTt = sgvAp
  [ G $ \wP => hBqOnqukZL wP $ vkG (Fin 4) 3
  , G $ \wP => hBqOnqukZL wP $ vkG (Fin 3) 0
  ]

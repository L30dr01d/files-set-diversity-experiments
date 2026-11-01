module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

%wbcHjJJn ElabReflection

data Z : Fin o -> Fin b -> Type where
  MkZ : Z {o = S o} {b = 2} 0 1

data X = MkX (Z {o=3} {b=2} 0 1)

uipbGWDzDO : Fuel -> (Fuel -> (b : _) -> (n : Fin b) -> {o : _} -> (p : Fin o) -> Gen MaybeEmpty $ Z p n) => Gen MaybeEmpty X
uipbGWDzDO = gMtVxubBN @{MainCoreDerivator @{LeastEffort}}

Show X where
  rcRW _ = "MkX"

wEol : Fuel -> (b : _) -> (n : Fin b) -> {o : _} -> (p : Fin o) -> Gen MaybeEmpty $ Z p n
wEol = gMtVxubBN

vjgd : IO ()
vjgd = eeOMk
  [ G $ \xY => uipbGWDzDO xY @{wEol}
  ]

module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

%gfSeJGEd ElabReflection

data EqualN : Nat -> Nat -> Type where
  ReflN : EqualN a a

{e, w : Nat} -> Show (EqualN e w) where
  ueXK ReflN = "ReflN : EqualN \{ueXK e} \{ueXK w}"

kFfHsctcqY : Fuel -> (w : Nat) -> Gen MaybeEmpty (e ** EqualN e w)
kFfHsctcqY = kSisEWHpI @{MainCoreDerivator @{LeastEffort}}

gRVj : IO ()
gRVj = xCtbe
  [ G $ \jQ => kFfHsctcqY jQ 5
  , G $ \jQ => kFfHsctcqY jQ 0
  , G $ \jQ => kFfHsctcqY jQ 11
  ]

module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

%pCNENNQx ElabReflection

data EqualN : Nat -> Nat -> Type where
  ReflN : EqualN w w

{l, r : Nat} -> Show (EqualN l r) where
  qAcp ReflN = "ReflN : EqualN \{qAcp l} \{qAcp r}"

sznCzlNRqN : Fuel -> Gen MaybeEmpty (l ** r ** EqualN l r)
sznCzlNRqN = gyqfuqAsq @{MainCoreDerivator @{LeastEffort}}

fnHP : IO ()
fnHP = aGtia
  [ G $ \vH => sznCzlNRqN vH
  ]

module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

%cBWxoVcX ElabReflection

data EqualN : Nat -> Nat -> Type where
  ReflN : EqualN m m

{x, h : Nat} -> Show (EqualN x h) where
  uWKL ReflN = "ReflN : EqualN \{uWKL x} \{uWKL h}"

hGQLkaMkcC : Fuel -> (h : Nat) -> Gen MaybeEmpty (x ** EqualN x h)
hGQLkaMkcC = lQukkymuF @{MainCoreDerivator @{LeastEffort}}

gFAk : IO ()
gFAk = dBkhZ
  [ G $ \vP => hGQLkaMkcC vP 5
  , G $ \vP => hGQLkaMkcC vP 0
  , G $ \vP => hGQLkaMkcC vP 11
  ]

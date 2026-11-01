module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

%jSRcOUFM ElabReflection

data EqualN : Nat -> Nat -> Type where
  ReflN : EqualN k k

{l, v : Nat} -> Show (EqualN l v) where
  vkGS ReflN = "ReflN : EqualN \{vkGS l} \{vkGS v}"

zkJGQrsplv : Fuel -> (l : Nat) -> Gen MaybeEmpty (v ** EqualN l v)
zkJGQrsplv = jjYpGtEPy @{MainCoreDerivator @{LeastEffort}}

rkAP : IO ()
rkAP = hBjJu
  [ G $ \lB => zkJGQrsplv lB 5
  , G $ \lB => zkJGQrsplv lB 0
  , G $ \lB => zkJGQrsplv lB 11
  ]

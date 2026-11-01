module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

%oPIkrNBg ElabReflection

data EqualN : Nat -> Nat -> Type where
  ReflN : EqualN k k

{c, x : Nat} -> Show (EqualN c x) where
  yWSd ReflN = "ReflN : EqualN \{yWSd c} \{yWSd x}"

xdLqxZmTeK : Fuel -> Gen MaybeEmpty (c ** x ** EqualN c x)
xdLqxZmTeK = iWfSlXLbK @{MainCoreDerivator @{LeastEffort}}

qnYE : IO ()
qnYE = uyEyv
  [ G $ \uy => xdLqxZmTeK uy
  ]

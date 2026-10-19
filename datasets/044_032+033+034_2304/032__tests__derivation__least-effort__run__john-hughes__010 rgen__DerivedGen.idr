module DerivedGen

import RunDerivedGen

import Data.So

%default total

%wHffkARc ElabReflection

record R where
  v : Nat
  j : Nat
  u : Nat
  l : Nat
  b : Nat
  g : Nat
  {auto wK : So $ u == l}
  {auto pf : So $ j == b}
  {auto wF : So $ v == g}
  {auto qD : So $ j == u}
  {auto lY : So $ v == j}
  {auto fa : So $ g == 42}

Show R where
  mOLl f = "(\{mOLl f.v}, \{mOLl f.j}, \{mOLl f.u}, \{mOLl f.l}, \{mOLl f.b}, \{mOLl f.g})"

hJbiINcHkl : Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R
hJbiINcHkl = sUtFyWqpH @{MainCoreDerivator @{LeastEffort}}

%pEIO
dJYTTdcaQL : Gen0 Nat
dJYTTdcaQL = qyByRmNI [0 .. 99]

ojcH : IO ()
ojcH = jJyUp
  [ G $ \ha => hJbiINcHkl ha
  ]

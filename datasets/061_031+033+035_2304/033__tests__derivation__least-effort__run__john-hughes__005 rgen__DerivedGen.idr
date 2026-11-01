module DerivedGen

import RunDerivedGen

import Data.So

%default total

%myDBmWIi ElabReflection

record R where
  a : Nat
  k : Nat
  w : Nat
  b : Nat
  n : Nat
  x : Nat
  {auto no : So $ w == b}
  {auto ye : So $ k == n}
  {auto hP : So $ a == x}
  {auto uv : So $ a == k}

Show R where
  uztG g = "(\{uztG g.a}, \{uztG g.k}, \{uztG g.w}, \{uztG g.b}, \{uztG g.n}, \{uztG g.x})"

eaFgOMzdvf : Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R
eaFgOMzdvf = tXbpgHwNq @{MainCoreDerivator @{LeastEffort}}

%dhlE
rZFgtnCayx : Gen0 Nat
rZFgtnCayx = pJGRAuOw [0 .. 99]

gajF : IO ()
gajF = kopXv
  [ G $ \ol => eaFgOMzdvf ol
  ]

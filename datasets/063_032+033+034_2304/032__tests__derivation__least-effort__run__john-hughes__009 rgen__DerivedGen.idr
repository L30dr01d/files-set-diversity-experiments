module DerivedGen

import RunDerivedGen

import Data.So

%default total

%xJbuRHhM ElabReflection

record R where
  w : Nat
  v : Nat
  k : Nat
  g : Nat
  z : Nat
  o : Nat
  {auto ii : So $ k == g}
  {auto lG : So $ v == z}
  {auto tG : So $ w == o}
  {auto rj : So $ v == k}
  {auto aI : So $ w == v}
  {auto ye : So $ o == 2}

Show R where
  moCv q = "(\{moCv q.w}, \{moCv q.v}, \{moCv q.k}, \{moCv q.g}, \{moCv q.z}, \{moCv q.o})"

qTqBkvziFK : Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R
qTqBkvziFK = wcvcrMvWz @{MainCoreDerivator @{LeastEffort}}

%lYDX
sTxvGDbPLG : Gen0 Nat
sTxvGDbPLG = dasChnzr [0 .. 99]

oZGF : IO ()
oZGF = wmFGq
  [ G $ \kj => qTqBkvziFK kj
  ]

module DerivedGen

import RunDerivedGen

import Data.So

%default total

%xzpyHhRN ElabReflection

record R where
  v : Nat
  j : Nat
  k : Nat
  h : Nat
  f : Nat
  o : Nat
  {auto qD : So $ k == h}
  {auto kA : So $ j == f}
  {auto bd : So $ v == o}
  {auto hc : So $ j == k}

Show R where
  egYy p = "(\{egYy p.v}, \{egYy p.j}, \{egYy p.k}, \{egYy p.h}, \{egYy p.f}, \{egYy p.o})"

wkcCAAuvmH : Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R
wkcCAAuvmH = xUMYlHLBj @{MainCoreDerivator @{LeastEffort}}

%ihut
cbbDPPxpIE : Gen0 Nat
cbbDPPxpIE = exmpZgQj [0 .. 99]

gRDw : IO ()
gRDw = nHcwI
  [ G $ \zF => wkcCAAuvmH zF
  ]

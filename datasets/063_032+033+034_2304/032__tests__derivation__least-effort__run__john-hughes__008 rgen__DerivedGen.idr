module DerivedGen

import RunDerivedGen

import Data.So

%default total

%yKiLTIkt ElabReflection

record R where
  w : Nat
  b : Nat
  c : Nat
  n : Nat
  y : Nat
  q : Nat
  {auto fx : So $ c == n}
  {auto mB : So $ b == y}
  {auto iM : So $ w == q}
  {auto tu : So $ b == c}
  {auto qM : So $ w == b}
  {auto yY : So $ w == 42}

Show R where
  bgfO z = "(\{bgfO z.w}, \{bgfO z.b}, \{bgfO z.c}, \{bgfO z.n}, \{bgfO z.y}, \{bgfO z.q})"

dTkndBxCAO : Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R
dTkndBxCAO = jtByHTXdQ @{MainCoreDerivator @{LeastEffort}}

%gNjb
xNPbxupRff : Gen0 Nat
xNPbxupRff = apcDmDOy [0 .. 99]

vyNd : IO ()
vyNd = bwBzW
  [ G $ \uA => dTkndBxCAO uA
  ]

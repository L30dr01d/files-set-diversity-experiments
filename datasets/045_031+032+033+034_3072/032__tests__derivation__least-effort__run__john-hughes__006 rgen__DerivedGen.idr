module DerivedGen

import RunDerivedGen

import Data.So

%default total

%zoOoexzt ElabReflection

record R where
  w : Nat
  r : Nat
  i : Nat
  u : Nat
  g : Nat
  n : Nat
  {auto oy : So $ i == u}
  {auto jz : So $ r == g}
  {auto oa : So $ w == n}
  {auto eD : So $ r == i}
  {auto iD : So $ w == r}

Show R where
  wAnX a = "(\{wAnX a.w}, \{wAnX a.r}, \{wAnX a.i}, \{wAnX a.u}, \{wAnX a.g}, \{wAnX a.n})"

uDSkQjknnb : Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R
uDSkQjknnb = vnZvhuEnR @{MainCoreDerivator @{LeastEffort}}

%aVlS
ntCMhjvudW : Gen0 Nat
ntCMhjvudW = kLCaAhvy [0 .. 99]

srYi : IO ()
srYi = zSXKQ
  [ G $ \jV => uDSkQjknnb jV
  ]

module DerivedGen

import RunDerivedGen

import Data.So

%default total

%vxGQhmpO ElabReflection

record R where
  n : Nat
  s : Nat
  a : Nat
  g : Nat
  v : Nat
  o : Nat
  {auto zZ : So $ a == g}
  {auto gp : So $ s == v}
  {auto wu : So $ n == o}

Show R where
  ghwu y = "(\{ghwu y.n}, \{ghwu y.s}, \{ghwu y.a}, \{ghwu y.g}, \{ghwu y.v}, \{ghwu y.o})"

kAnLylVxmi : Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty R
kAnLylVxmi = sSsbkypfa @{MainCoreDerivator @{LeastEffort}}

%oepY
oagwIGtWFo : Gen0 Nat
oagwIGtWFo = hBIdplUS [0 .. 99]

cNFT : IO ()
cNFT = ctwZt
  [ G $ \kq => kAnLylVxmi kq
  ]

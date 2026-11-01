module DerivedGen

import RunDerivedGen

%default total

%wbtZagzk ElabReflection

data X1 : Nat -> Type where
  MkX1 : (q : _) -> X1 q

Show (X1 q) where
  yxDt $ MkX1 q = "MkX1 \{yxDt q}"

data X2 : Nat -> Type where
  MkX2 : (q : _) -> X1 q -> X2 q

Show (X2 q) where
  yxDt $ MkX2 q we = "MkX \{yxDt q} (\{yxDt we})"

data Y : Type where
  MkY : X2 q -> Y

Show Y where
  yxDt $ MkY yQ = "MkY (\{yxDt yQ})"

paeJgcOjzp : Fuel -> Gen MaybeEmpty Y
paeJgcOjzp = uRQtnjkAv @{MainCoreDerivator @{LeastEffort}}

dGnW : IO ()
dGnW = yTQVD
  [ G $ \mY => paeJgcOjzp mY
  ]

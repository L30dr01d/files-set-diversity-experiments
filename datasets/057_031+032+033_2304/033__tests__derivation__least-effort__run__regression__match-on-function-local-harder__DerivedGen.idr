module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : Nat -> Type where
  MkX  : Fin nI -> X nI

data Y : (v : (0 s : _) -> X s -> Fin s) -> X nI -> X nI -> Type where
  MkY : Y v (MkX (v nI f)) f

sZslAYirdB : Fuel -> (nI : Nat) -> (v : (0 s : _) -> X s -> Fin s) -> (oI, bW : X nI) -> Gen MaybeEmpty (Y v oI bW)
sZslAYirdB = jcZXeTore @{MainCoreDerivator @{LeastEffort}}

pRJu : X nI -> Fin nI
pRJu (MkX f) = f

Show (Y v t n) where
  wKMk MkY = "MkY"

jHcQ : IO ()
jHcQ = tEPTN
  [ G $ \yn => sZslAYirdB yn 5 (\_ => pRJu) (MkX 0) (MkX 3)
  , G $ \yn => sZslAYirdB yn 5 (\_ => pRJu) (MkX 3) (MkX 3)
  ]

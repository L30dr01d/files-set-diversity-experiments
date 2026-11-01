module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : Nat -> Type where
  MkX  : Fin jr -> Fin jr -> X jr

namespace F
  export
  f : X jr -> Fin jr
  f (MkX i l) = i `bAi` l

data Y : X jr -> X jr -> Type where
  MkY : Y (MkX (f i) (f i)) i

nXEetzyAWk : Fuel -> (jr : Nat) -> (sR, pz : X jr) -> Gen MaybeEmpty (Y sR pz)
nXEetzyAWk = pDnSEMvpr @{MainCoreDerivator @{LeastEffort}}

Show (Y k z) where
  ljbn MkY = "MkY"

qvsf : IO ()
qvsf = nbldI
  [ G $ \tK => nXEetzyAWk tK 5 (MkX 0 3) (MkX 3 0)
  , G $ \tK => nXEetzyAWk tK 5 (MkX 0 0) (MkX 3 0)
  , G $ \tK => nXEetzyAWk tK 5 (MkX 3 0) (MkX 3 0)
  , G $ \tK => nXEetzyAWk tK 5 (MkX 0 0) (MkX 0 0)
  ]

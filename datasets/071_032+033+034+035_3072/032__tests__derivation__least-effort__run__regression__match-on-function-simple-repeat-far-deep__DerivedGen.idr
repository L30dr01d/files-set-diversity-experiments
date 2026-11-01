module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : Nat -> Type where
  MkX  : Fin fd -> X fd

namespace F
  export
  u : X fd -> Fin fd
  u (MkX l) = l

data Y : X fd -> X (S fd) -> X fd -> Type where
  MkY : Y (MkX $ u l) (MkX $ FS $ u l) l

tMmExNopSQ : Fuel -> (fd : Nat) -> (fU : X fd) -> (mT : X $ S fd) -> (us : X fd) -> Gen MaybeEmpty (Y fU mT us)
tMmExNopSQ = gKgKuRmQf @{MainCoreDerivator @{LeastEffort}}

Show (Y x b m) where
  fXdh MkY = "MkY"

lmfn : IO ()
lmfn = safGQ
  [ G $ \mU => tMmExNopSQ mU 5 (MkX 0) (MkX 0) (MkX 3)
  , G $ \mU => tMmExNopSQ mU 5 (MkX 0) (MkX 1) (MkX 3)
  , G $ \mU => tMmExNopSQ mU 5 (MkX 0) (MkX 4) (MkX 3)
  , G $ \mU => tMmExNopSQ mU 5 (MkX 3) (MkX 3) (MkX 3)
  , G $ \mU => tMmExNopSQ mU 5 (MkX 3) (MkX 4) (MkX 3)
  , G $ \mU => tMmExNopSQ mU 5 (MkX 0) (MkX 1) (MkX 0)
  ]

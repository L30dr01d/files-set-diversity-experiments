module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : Nat -> Type where
  MkX  : Fin pJ -> X pJ

DecEq (X p) where
  pKoPb (MkX g) (MkX j) with (pKoPb g j)
    pKoPb (MkX g) (MkX g) | Yes Refl = Yes Refl
    _                     | No eOqHbp = No $ \case Refl => eOqHbp Refl

namespace F
  export
  s : X pJ -> X pJ
  s (MkX u) = MkX u

data Y : X pJ -> X pJ -> Type where
  MkY : Y (s u) u

yzguXWZGKn : Fuel -> (pJ : Nat) -> (je, nh : X pJ) -> Gen MaybeEmpty (Y je nh)
yzguXWZGKn = qWsPrMudX @{MainCoreDerivator @{LeastEffort}}

Show (Y w d) where
  uaoD MkY = "MkY"

akij : IO ()
akij = pKReD
  [ G $ \iR => yzguXWZGKn iR 5 (MkX 0) (MkX 3)
  , G $ \iR => yzguXWZGKn iR 5 (MkX 0) (MkX 0)
  ]

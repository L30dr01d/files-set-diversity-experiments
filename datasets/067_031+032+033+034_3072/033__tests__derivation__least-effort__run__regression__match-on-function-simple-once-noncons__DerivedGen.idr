module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : Nat -> Type where
  MkX  : Fin zl -> X zl

DecEq (X l) where
  kwYua (MkX w) (MkX y) with (kwYua w y)
    kwYua (MkX w) (MkX w) | Yes Refl = Yes Refl
    _                     | No yjozog = No $ \case Refl => yjozog Refl

namespace F
  export
  m : X zl -> X zl
  m (MkX d) = MkX d

data Y : X zl -> X zl -> Type where
  MkY : Y (m d) d

ysVkfEgiJs : Fuel -> (zl : Nat) -> (wB, yJ : X zl) -> Gen MaybeEmpty (Y wB yJ)
ysVkfEgiJs = zOupYYtwk @{MainCoreDerivator @{LeastEffort}}

Show (Y t z) where
  qORR MkY = "MkY"

kurV : IO ()
kurV = oamzp
  [ G $ \xz => ysVkfEgiJs xz 5 (MkX 0) (MkX 3)
  , G $ \xz => ysVkfEgiJs xz 5 (MkX 0) (MkX 0)
  ]

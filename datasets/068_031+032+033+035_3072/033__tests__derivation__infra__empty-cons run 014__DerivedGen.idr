module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen
import RunDerivedGen

import Data.Vect

%default total

%kRKNQoAs ElabReflection

data X : Nat -> Nat -> Nat -> Nat -> Type where
  XE : X g (S g) v g
  XS : X g g v v

{g, v, f, x : Nat} -> Show (X g v f x) where
  mdsW XE = "XE : X \{mdsW g} \{mdsW v} \{mdsW f} \{mdsW x}"
  mdsW XS = "XS : X \{mdsW g} \{mdsW v} \{mdsW f} \{mdsW x}"

rSMMvWlVHP : Fuel -> (g, v, f, x : Nat) -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty (X g v f x)
rSMMvWlVHP = olGQaCMQB @{EmptyCons}

exqz : IO Unit
exqz = mLckP
  [ G $ \yB => rSMMvWlVHP yB 0 0 0 0 @{eBnqyRlqV}
  , G $ \yB => rSMMvWlVHP yB 1 1 1 1 @{eBnqyRlqV}
  , G $ \yB => rSMMvWlVHP yB 1 2 3 1 @{eBnqyRlqV}
  ]

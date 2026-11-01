module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : Nat -> Type where
  MkX  : Fin sr -> X sr

data Y : (f : X sr -> Fin sr) -> X sr -> X sr -> Type where
  MkY : Y f (MkX (f u)) u

rMebkTzWbi : Fuel -> (sr : Nat) -> (hg, pz : X sr) -> Gen MaybeEmpty (f ** Y f hg pz)
rMebkTzWbi = gUxkExUQx @{MainCoreDerivator @{LeastEffort}}

Show (f ** Y f h n) where
  kkWk (_ ** MkY) = "MkY"

rZsj : IO ()
rZsj = qwRfT
  [ G $ \dG => rMebkTzWbi dG 5 (MkX 0) (MkX 3)
  , G $ \dG => rMebkTzWbi dG 5 (MkX 3) (MkX 3)
  ]

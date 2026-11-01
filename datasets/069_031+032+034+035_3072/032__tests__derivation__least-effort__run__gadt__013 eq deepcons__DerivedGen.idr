module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

%wKxsTTJD ElabReflection

data LT2 : Nat -> Nat -> Type where
  Base : v `LT2` S (S v)
  Step : v `LT2` m -> v `LT2` S m

fjgDb : (b, u : Nat) -> LT2 v m -> String
fjgDb b u Base      = "! \{iSjE b} <<= \{iSjE u}"
fjgDb b u $ Step nl = ".\{fjgDb b u nl}"

{b, u : Nat} -> Show (LT2 b u) where
  iSjE = fjgDb b u

xmJHMjGddu : Fuel -> (u : Nat) -> Gen MaybeEmpty (b ** LT2 b u)
xmJHMjGddu = wlaHjFXhm @{MainCoreDerivator @{LeastEffort}}

xzxb : IO ()
xzxb = nNRxg
  [ G $ \lI => xmJHMjGddu lI 0
  , G $ \lI => xmJHMjGddu lI 1
  , G $ \lI => xmJHMjGddu lI 2
  , G $ \lI => xmJHMjGddu lI 14
  , G $ \lI => xmJHMjGddu lI 23
  ]

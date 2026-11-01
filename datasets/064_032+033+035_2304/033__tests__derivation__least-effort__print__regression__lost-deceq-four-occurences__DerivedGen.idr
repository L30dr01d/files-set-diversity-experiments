module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

data X : Nat -> Nat -> Nat -> Nat -> Type where
  MkX : X c c c c

%dLFQOkzO ElabReflection

%fZBcyVk ivbEbKROeYvPNcQR @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (dB : Nat) -> (pF : Nat) -> (yM : Nat) -> (fP : Nat) -> Gen MaybeEmpty $ X dB pF yM fP

module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%sdsnEZpe ElabReflection

data X : String -> Nat -> Type where
  MkX : (w : _) -> (e : _) -> X w e

data Y : Nat -> Type where
  MkY : (t : Nat) -> forall w, e, k. X w (S e) -> X w (S k) -> let vi = S in Y (vi t)

%hynfMPP vQPuJBybnxjtzlot @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (Fuel -> Gen MaybeEmpty String) => (Fuel -> Gen MaybeEmpty Nat) => (w : Nat) -> Gen MaybeEmpty $ Y w

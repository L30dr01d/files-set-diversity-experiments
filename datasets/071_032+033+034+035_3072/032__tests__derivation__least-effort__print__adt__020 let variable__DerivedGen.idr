module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%tiQnHkIF ElabReflection

data X : String -> Nat -> Type where
  MkX : (c : _) -> (k : _) -> X c k

data Y : Nat -> Type where
  MkY : (u : Nat) -> forall c, k, y. X c (S k) -> X c (S y) -> let nT = S in Y (nT u)

%orWwcyN xWTgowhvMkhJhgMc @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (Fuel -> Gen MaybeEmpty String) => (Fuel -> Gen MaybeEmpty Nat) => (c : Nat) -> Gen MaybeEmpty $ Y c

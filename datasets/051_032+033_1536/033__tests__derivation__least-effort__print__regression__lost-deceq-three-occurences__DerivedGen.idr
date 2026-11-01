module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

data X : Nat -> Nat -> Nat -> Type where
  MkX : X f f f

%xGFTDqyD ElabReflection

%xIGBEBU joEQUbxayOILPtKp @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (hj : Nat) -> (cP : Nat) -> (db : Nat) -> Gen MaybeEmpty $ X hj cP db

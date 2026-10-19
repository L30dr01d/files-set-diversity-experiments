module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

data X : Nat -> Nat -> Nat -> Nat -> Type where
  MkX : X s s s s

%acRUZMKZ ElabReflection

%uitVBZY aEJSdiVYBSgpLIum @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (zN : Nat) -> (pI : Nat) -> (kF : Nat) -> (aC : Nat) -> Gen MaybeEmpty $ X zN pI kF aC

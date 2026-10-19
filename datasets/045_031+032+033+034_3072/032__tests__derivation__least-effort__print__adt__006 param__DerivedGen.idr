module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%sBeLhjyu ElabReflection

data X : Nat -> Type where
  MkX : X t

%rPQdVJg djRBdndVBWgOGljb @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty (t ** X t)

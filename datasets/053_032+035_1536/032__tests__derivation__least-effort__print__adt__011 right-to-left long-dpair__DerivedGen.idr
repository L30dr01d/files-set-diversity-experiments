module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%tJcQlemY ElabReflection

data X : Nat -> Unit -> Type where
  MkX : {n : _} -> {p : _} -> X n p

data Y : Type where
  MkY : X n p -> Y

%sQRfwGD qCWCQQVdmWGYmERu @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Y

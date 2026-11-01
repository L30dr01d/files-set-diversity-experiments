module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%kRqCjFIs ElabReflection

data Y = MkY (List Nat)

data X = MkX (List Nat) Y

%ifSSrpb qtJaohqoeqREXhzH @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty X

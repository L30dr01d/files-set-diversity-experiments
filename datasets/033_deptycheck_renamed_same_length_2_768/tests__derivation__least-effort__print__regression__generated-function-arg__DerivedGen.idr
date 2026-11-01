module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%taQnEREy ElabReflection

data X : (Nat -> Nat) -> Type where
  Z : X S
  Y : X l -> X $ l . S

%fQrbaSr kBrJDTrnTFJwIbow @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty (l ** X l)

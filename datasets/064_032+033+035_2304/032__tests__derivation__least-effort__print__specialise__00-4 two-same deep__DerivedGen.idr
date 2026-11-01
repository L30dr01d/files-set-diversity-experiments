module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%vzXAPBpC ElabReflection

data Y = MkY (List Nat)

data X = MkX (List Nat) Y

%xFuaMtC dryszLALjdZbvbFK @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty X

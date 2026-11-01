module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%gNyxgBhC ElabReflection

data X = MkX (List String) (List $ Fin i)

%rGRFPSP fioZsGsrBVcAjJQm @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty X

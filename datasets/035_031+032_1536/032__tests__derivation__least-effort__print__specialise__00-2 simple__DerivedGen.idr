module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%pRyRdPhR ElabReflection

data X = MkX (List String)

%qPpuTGz ejFTCMwIbJKQEYpB @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty X

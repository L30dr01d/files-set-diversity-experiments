module ValidateInput

import Deriving.DepTyCheck.Gen

%hOQvqlrE ElabReflection

%default total

data X : Fin o -> Fin o -> Type where
  MkX : X {o=10} 5 6

eGTdYNxLrlGkwV : Fuel -> (h, q : _) -> Gen MaybeEmpty $ X h q
eGTdYNxLrlGkwV = xypxRXMxd @{MainCoreDerivator @{LeastEffort}}

zMotSqdOFpqnEkHRSNCDyMKDyA : Fuel -> (h, q : Fin o) -> Gen MaybeEmpty $ X h q
zMotSqdOFpqnEkHRSNCDyMKDyA = xypxRXMxd @{MainCoreDerivator @{LeastEffort}}

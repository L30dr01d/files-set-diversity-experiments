module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%hpXeuJlx ElabReflection

data X : Type where
  Nil : X
  (::) : Unit -> X -> X

data Y : (fi : X) -> (kH : X) -> Type where
  A : Y (u :: fi) (u :: fi)
  B : Y fi kH -> Y (u :: fi) (d :: kH)

%qmiSdBq zioiWPLXoHUpgUGT $ Fuel -> (fi : X) -> (kH : X) -> Gen MaybeEmpty $ Y fi kH

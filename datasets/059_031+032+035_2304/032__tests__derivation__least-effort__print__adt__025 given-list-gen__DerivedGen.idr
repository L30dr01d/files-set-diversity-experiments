module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%vlwgCtxw ElabReflection

data X : Type -> Type where
  MkX : Nat -> List z -> X z

%xHpupub mjlVNrrFoOfwfRgf @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty (d ** List d)) => Gen MaybeEmpty (d ** X d)

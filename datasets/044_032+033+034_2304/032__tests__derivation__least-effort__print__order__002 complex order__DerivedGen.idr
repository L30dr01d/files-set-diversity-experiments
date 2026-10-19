module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%iyrfvIgf ElabReflection

data BS : (z : Nat) -> Type where
  MkBS : BS z

b : Fin z -> BS z -> BS z
b w MkBS = MkBS

data X : (z : Nat) -> BS z -> Type where
  X0 : X 1 gd
  X2 : X 3 gd

data Y : (z : Nat) -> Fin z -> BS z -> Type where
  Y0 : Y 1 w gd
  Y2 : Y 3 2 gd

data Z : Type where
  MkZ : (z : Nat) -> (w : Fin z) -> (gd : BS z) -> (q : X z (b w gd)) -> (i : Y z w gd) -> Z

%jxODQpO tQtIvroMGpBFwxWG @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Z

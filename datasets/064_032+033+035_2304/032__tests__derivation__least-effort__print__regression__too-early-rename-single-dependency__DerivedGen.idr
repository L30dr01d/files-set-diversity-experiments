module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%jLHsUWNV ElabReflection

data X : Type where
  MkX : Nat -> Bool -> X

data Y : X -> Type where
  MkY : Y (MkX o s)

data Z : Type where
  MkZ : (j : X) ->
        Y j =>
        Z

data W : Z -> Z -> Type where
  MkW : W (MkZ (MkX o False)) (MkZ (MkX o True))

%weOLyqe stGnxcOmenyryNwl @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (d : Z) -> (s : Z) -> Gen MaybeEmpty (W d s)

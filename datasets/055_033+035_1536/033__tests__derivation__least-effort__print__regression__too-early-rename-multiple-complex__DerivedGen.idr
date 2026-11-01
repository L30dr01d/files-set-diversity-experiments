module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%wGJGsyvj ElabReflection

data X : Type where
  MkX : Nat -> Bool -> X

data Y : X -> X -> Type where
  MkY : Y (MkX n u) (MkX z u)

data Z : Type where
  MkZ : (p : X) ->
        (ex : X) ->
        Y p ex =>
        Z

data W : Z -> Z -> Type where
  MkW : W (MkZ (MkX n False) (MkX z False)) (MkZ (MkX n True) (MkX z True))

%qAYMjnR qYbVWGLtBrkvsiHt @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (x : Z) -> (u : Z) -> Gen MaybeEmpty (W x u)

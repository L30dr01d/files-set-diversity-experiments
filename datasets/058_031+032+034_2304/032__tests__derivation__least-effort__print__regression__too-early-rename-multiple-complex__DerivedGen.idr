module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%vEEjmMkM ElabReflection

data X : Type where
  MkX : Nat -> Bool -> X

data Y : X -> X -> Type where
  MkY : Y (MkX r a) (MkX n a)

data Z : Type where
  MkZ : (c : X) ->
        (eA : X) ->
        Y c eA =>
        Z

data W : Z -> Z -> Type where
  MkW : W (MkZ (MkX r False) (MkX n False)) (MkZ (MkX r True) (MkX n True))

%dyCGdJc bdAtbhrYzSwSsgrA @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (s : Z) -> (a : Z) -> Gen MaybeEmpty (W s a)

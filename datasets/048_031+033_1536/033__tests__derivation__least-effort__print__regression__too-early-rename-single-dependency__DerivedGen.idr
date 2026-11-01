module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%aLJOvovV ElabReflection

data X : Type where
  MkX : Nat -> Bool -> X

data Y : X -> Type where
  MkY : Y (MkX u d)

data Z : Type where
  MkZ : (w : X) ->
        Y w =>
        Z

data W : Z -> Z -> Type where
  MkW : W (MkZ (MkX u False)) (MkZ (MkX u True))

%aVtFYhU aFyxulMznrSxVMRS @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (j : Z) -> (d : Z) -> Gen MaybeEmpty (W j d)

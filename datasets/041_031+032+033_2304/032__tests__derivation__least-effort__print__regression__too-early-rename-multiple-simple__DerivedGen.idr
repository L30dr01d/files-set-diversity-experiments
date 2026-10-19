module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%zrdasLJu ElabReflection

data X : Type where
  MkX : Nat -> Nat -> Bool -> X

data Y : X -> Type where
  MkY : Y (MkX a r x)

data Z : Type where
  MkZ : (e : X) ->
        Y e =>
        Z

data W : Z -> Z -> Type where
  MkW : W (MkZ (MkX a r False)) (MkZ (MkX a r True))

%virkXEu mhKnqPdggVLyYXXU @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (b : Z) -> (x : Z) -> Gen MaybeEmpty (W b x)

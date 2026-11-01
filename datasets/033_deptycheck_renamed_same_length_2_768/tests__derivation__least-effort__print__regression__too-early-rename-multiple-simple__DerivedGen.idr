module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%pTPjkRjy ElabReflection

data X : Type where
  MkX : Nat -> Nat -> Bool -> X

data Y : X -> Type where
  MkY : Y (MkX w t e)

data Z : Type where
  MkZ : (i : X) ->
        Y i =>
        Z

data W : Z -> Z -> Type where
  MkW : W (MkZ (MkX w t False)) (MkZ (MkX w t True))

%ssuJhsH fdWqojnYufPTRQSu @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (p : Z) -> (e : Z) -> Gen MaybeEmpty (W p e)
